//! Rational (Z[1/2]) flip-graph exploration seeded at the DPS
//! <4x4x4:48> scheme (the only rank-48 class with real points).
//!
//! The seed is flip-isolated (no two summands share a factor up to
//! scalar in any slot), so the walk is the Moosbauer–Poole cycle
//! supercharged by scalar freedom:
//!   split : replace A_i (x) B_i (x) C_i by
//!           (mu A_k) (x) B_i (x) C_i  +  (A_i - mu A_k) (x) B_i (x) C_i
//!           — engineered mobility against ANY other summand k; rank +1.
//!   flip  : for a_i ~ a_j (proportional):  fold scalars, then
//!           (B_i += lam B_j) with (C_j -= lam' C_i) preserving the sum;
//!           lam in ±{1, 2, 1/2} (and the symmetric slot versions).
//!   reduce: a_i ~ a_j AND b_i ~ b_j  ->  merge into one summand
//!           (rank −1).  At rank <= 47 this is a WORLD-RECORD alarm:
//!           dump, verify, scream.
//!
//! Every summand is kept in canonical gauge (A, B primitive integer
//! vectors, leading sign +; C carries the dyadic scalar).  The engine
//! verifies exact sum preservation against the matmul tensor at every
//! checkpoint (i128 fixed-point, scale 2^24), rejects moves that push
//! any numerator past a magnitude cap, and collects distinct rank-48
//! canonical forms with odd-prime fingerprints for novelty screening.
//!
//! Usage: flip48 [--dir matmul/dps48] [--seconds N] [--threads N]
//!               [--cap 64] [--out found48q]
//!        flip48 --pursue6 ... [--resume6 FRONTIER.txt --startlevel N]
//!               lossless chase resume from a full-frontier dump
//!        flip48 --nmrand K [--n 2000]   random-walk nearmiss baseline
//!               (control for the --pursue6 gradient; depths 1..=K)
//!        flip48 --pursue5 ... [--resume]  logs completed parent indices
//!               to OUT/fringe_done.txt; --resume skips exactly those
//!               (sound under work-stealing: done-set is not a prefix)

use rayon::prelude::*;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

const SC: i128 = 1 << 24; // fixed-point scale for exact verification

// ---------- dyadic vectors ----------
// value = 2^exp * nums (nums primitive: gcd odd, i.e. not all even)
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct Vec16 {
    nums: [i64; 16],
    exp: i32,
}

impl Vec16 {
    fn zero() -> Self {
        Vec16 { nums: [0; 16], exp: 0 }
    }
    fn is_zero(&self) -> bool {
        self.nums.iter().all(|&x| x == 0)
    }
    fn normalize(mut self) -> Self {
        if self.is_zero() {
            self.exp = 0;
            return self;
        }
        // pull out common powers of two into exp
        let mut tz = i32::MAX;
        for &x in self.nums.iter().filter(|x| **x != 0) {
            tz = tz.min(x.trailing_zeros() as i32);
        }
        if tz > 0 {
            for x in self.nums.iter_mut() {
                *x >>= tz;
            }
            self.exp += tz;
        }
        self
    }
    /// FULL-content canonical form: self = sign * 2^exp * g * prim,
    /// with g odd (> 0), prim primitive (content 1), leading coeff > 0.
    /// v1 extracted only powers of two, which made proportionality by
    /// odd factors (3, 5, ...) invisible to flips and reductions.
    fn canon(&self) -> (Vec16, bool, i32, i64) {
        fn gcd(a: i64, b: i64) -> i64 {
            let (mut a, mut b) = (a.abs(), b.abs());
            while b != 0 {
                let t = a % b;
                a = b;
                b = t;
            }
            a
        }
        let mut v = self.clone().normalize();
        let mut neg = false;
        for &x in v.nums.iter() {
            if x != 0 {
                neg = x < 0;
                break;
            }
        }
        if neg {
            for x in v.nums.iter_mut() {
                *x = -*x;
            }
        }
        let mut g = 0i64;
        for &x in v.nums.iter() {
            g = gcd(g, x);
        }
        if g > 1 {
            for x in v.nums.iter_mut() {
                *x /= g;
            }
        } else {
            g = 1;
        }
        let e = v.exp;
        v.exp = 0;
        (v, neg, e, g)
    }
    /// self += lam * other, lam = sign * 2^k
    fn add_scaled(&self, other: &Vec16, neg: bool, k: i32) -> Option<Vec16> {
        let oe = other.exp + k;
        let e = self.exp.min(oe);
        let (sa, sb) = ((self.exp - e) as u32, (oe - e) as u32);
        if sa > 40 || sb > 40 {
            return None;
        }
        let mut nums = [0i64; 16];
        for i in 0..16 {
            let a = self.nums[i].checked_shl(sa)?;
            let b = other.nums[i].checked_shl(sb)?;
            nums[i] = if neg { a - b } else { a + b };
        }
        Some(Vec16 { nums, exp: e }.normalize())
    }
    fn max_abs(&self) -> i64 {
        self.nums.iter().map(|x| x.abs()).max().unwrap()
    }
}

#[derive(Clone)]
struct Summand {
    a: Vec16, // primitive, sign-normalized
    b: Vec16, // primitive, sign-normalized
    c: Vec16, // carries the dyadic scalar (any dyadic vector)
}

impl Summand {
    fn gauge(a: Vec16, b: Vec16, c: Vec16) -> Option<Summand> {
        if a.is_zero() || b.is_zero() || c.is_zero() {
            return None;
        }
        let (ca, na, ea, ga) = a.canon();
        let (cb, nb, eb, gb) = b.canon();
        let mut c = c.clone().normalize();
        c.exp += ea + eb;
        let g = ga.checked_mul(gb)?;
        for x in c.nums.iter_mut() {
            *x = x.checked_mul(g)?;
        }
        if na != nb {
            for x in c.nums.iter_mut() {
                *x = -*x;
            }
        }
        Some(Summand { a: ca, b: cb, c: c.normalize() })
    }
}

// ---------- exact verification ----------
fn verify(scheme: &[Summand]) -> bool {
    // sum_i a[x] b[y] c[z] == T[x,y,z] over the fixed-point scale
    // (exp handling: value = 2^exp * num; accumulate at common scale)
    for x in 0..16usize {
        let (ar, ac) = (x / 4, x % 4);
        for y in 0..16usize {
            let (br, bc) = (y / 4, y % 4);
            for z in 0..16usize {
                let (cr, cc) = (z / 4, z % 4);
                let mut s: i128 = 0;
                for t in scheme {
                    let e = t.a.exp + t.b.exp + t.c.exp;
                    let v = t.a.nums[x] as i128 * t.b.nums[y] as i128
                        * t.c.nums[z] as i128;
                    let sh = e + 24;
                    if sh < 0 || sh > 100 {
                        if v != 0 {
                            return false; // out of verification range
                        }
                        continue;
                    }
                    s += v << sh as u32;
                }
                let want = if ac == br && ar == cr && bc == cc {
                    SC
                } else {
                    0
                };
                if s != want {
                    return false;
                }
            }
        }
    }
    true
}

// ---------- rng ----------
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

// ---------- moves ----------
const LAMS: [(bool, i32); 6] =
    [(false, 0), (true, 0), (false, 1), (true, 1), (false, -1), (true, -1)];

/// slot accessor: 0 = a, 1 = b (flips on the c slot are covered by the
/// symmetric identities through a/b; splits cover all three via c too)
fn fac<'s>(t: &'s Summand, slot: usize) -> &'s Vec16 {
    match slot {
        0 => &t.a,
        1 => &t.b,
        _ => &t.c,
    }
}

/// flip on shared slot-`slot` factor of i, j: transfer in slot `tr`
/// (the other non-c slot or c), lambda = (neg, k).
/// identity (shared A): Bi' = Bi + lam Bj ; Cj' = Cj - lam Ci.
fn try_flip(
    scheme: &mut Vec<Summand>,
    i: usize,
    j: usize,
    slot: usize,
    lam: (bool, i32),
    cap: i64,
) -> bool {
    if i == j || fac(&scheme[i], slot) != fac(&scheme[j], slot) {
        return false;
    }
    // choose transfer slot: the two non-shared slots
    let others: [usize; 2] = match slot {
        0 => [1, 2],
        1 => [0, 2],
        _ => [0, 1],
    };
    let (t1, t2) = (others[0], others[1]);
    let (neg, k) = lam;
    let bi = fac(&scheme[i], t1).add_scaled(fac(&scheme[j], t1), neg, k);
    let cj = fac(&scheme[j], t2).add_scaled(fac(&scheme[i], t2), !neg, k);
    let (bi, cj) = match (bi, cj) {
        (Some(x), Some(y)) => (x, y),
        _ => return false,
    };
    if bi.is_zero() || cj.is_zero() || bi.max_abs() > cap || cj.max_abs() > cap {
        return false;
    }
    let mut ni = scheme[i].clone();
    let mut nj = scheme[j].clone();
    match t1 {
        0 => ni.a = bi,
        1 => ni.b = bi,
        _ => ni.c = bi,
    }
    match t2 {
        0 => nj.a = cj,
        1 => nj.b = cj,
        _ => nj.c = cj,
    }
    let (gi, gj) = (
        Summand::gauge(ni.a, ni.b, ni.c),
        Summand::gauge(nj.a, nj.b, nj.c),
    );
    match (gi, gj) {
        (Some(gi), Some(gj)) => {
            scheme[i] = gi;
            scheme[j] = gj;
            true
        }
        _ => false,
    }
}

/// split summand i against summand k in slot `slot` with mu = (neg, m):
/// factor_i = mu*factor_k + (factor_i - mu*factor_k); rank +1 and the
/// first part now SHARES slot `slot` with k.
fn try_split(
    scheme: &mut Vec<Summand>,
    i: usize,
    k: usize,
    slot: usize,
    mu: (bool, i32),
    cap: i64,
) -> bool {
    if i == k {
        return false;
    }
    let (neg, m) = mu;
    let fi = fac(&scheme[i], slot);
    let fk = fac(&scheme[k], slot);
    let rest = match fi.add_scaled(fk, !neg, m) {
        Some(r) => r,
        None => return false,
    };
    if rest.is_zero() || rest.max_abs() > cap {
        return false; // proportional (would be a reduction) or too big
    }
    // part 1: mu * fk in slot, other factors of i
    let mut part = Vec16 { nums: fk.nums, exp: fk.exp + m };
    if neg {
        for x in part.nums.iter_mut() {
            *x = -*x;
        }
    }
    let mk = |f: Vec16, t: &Summand| -> Option<Summand> {
        match slot {
            0 => Summand::gauge(f, t.b.clone(), t.c.clone()),
            1 => Summand::gauge(t.a.clone(), f, t.c.clone()),
            _ => Summand::gauge(t.a.clone(), t.b.clone(), f),
        }
    };
    let s1 = mk(part, &scheme[i]);
    let s2 = mk(rest, &scheme[i]);
    match (s1, s2) {
        (Some(s1), Some(s2)) => {
            scheme[i] = s1;
            scheme.push(s2);
            true
        }
        _ => false,
    }
}

/// reduction: i, j sharing ANY two slots (up to scalar) merge into
/// one summand on the third slot.  a and b are canon-normalized so
/// equality suffices there; c carries the scalar, so proportionality
/// on c is a canon comparison with the ratio folded into the merge.
fn try_reduce(scheme: &mut Vec<Summand>, cap: i64) -> bool {
    let n = scheme.len();
    for i in 0..n {
        for j in i + 1..n {
            let (si, sj) = (scheme[i].clone(), scheme[j].clone());
            // pattern ab: merge on c
            let merged: Option<Summand> = if si.a == sj.a && si.b == sj.b {
                sj.c.add_scaled(&si.c, false, 0).and_then(|c| {
                    if c.is_zero() {
                        None // handled below as rank -2
                    } else {
                        Summand::gauge(sj.a.clone(), sj.b.clone(), c)
                    }
                })
            } else if si.a == sj.a {
                // pattern ac: c_i = s_i chat, c_j = s_j chat ->
                // merge b' = s_i b_i + s_j b_j (sign/exp/odd content
                // from the full canon)
                let (ci, ni, ei, gi) = si.c.canon();
                let (cj, nj, ej, gj) = sj.c.canon();
                if ci == cj {
                    let mk = |v: &Vec16, e: i32, g: i64| -> Option<Vec16> {
                        let mut w = v.clone();
                        w.exp += e;
                        for x in w.nums.iter_mut() {
                            *x = x.checked_mul(g)?;
                        }
                        Some(w.normalize())
                    };
                    mk(&si.b, ei, gi)
                        .zip(mk(&sj.b, ej, gj))
                        .and_then(|(bi, bj)| {
                            bi.add_scaled(&bj, ni != nj, 0)
                        })
                        .and_then(|mut b| {
                            if ni {
                                for x in b.nums.iter_mut() {
                                    *x = -*x;
                                }
                            }
                            if b.is_zero() {
                                None
                            } else {
                                let mut cc = ci.clone();
                                cc.exp = 0;
                                Summand::gauge(sj.a.clone(), b, cc)
                            }
                        })
                } else {
                    None
                }
            } else if si.b == sj.b {
                // pattern bc: symmetric, merge a'
                let (ci, ni, ei, gi) = si.c.canon();
                let (cj, nj, ej, gj) = sj.c.canon();
                if ci == cj {
                    let mk = |v: &Vec16, e: i32, g: i64| -> Option<Vec16> {
                        let mut w = v.clone();
                        w.exp += e;
                        for x in w.nums.iter_mut() {
                            *x = x.checked_mul(g)?;
                        }
                        Some(w.normalize())
                    };
                    mk(&si.a, ei, gi)
                        .zip(mk(&sj.a, ej, gj))
                        .and_then(|(ai, aj)| {
                            ai.add_scaled(&aj, ni != nj, 0)
                        })
                        .and_then(|mut a| {
                            if ni {
                                for x in a.nums.iter_mut() {
                                    *x = -*x;
                                }
                            }
                            if a.is_zero() {
                                None
                            } else {
                                let mut cc = ci.clone();
                                cc.exp = 0;
                                Summand::gauge(a, sj.b.clone(), cc)
                            }
                        })
                } else {
                    None
                }
            } else {
                None
            };
            // exact-cancellation rank -2 case (ab pattern)
            if si.a == sj.a && si.b == sj.b {
                if let Some(c) = sj.c.add_scaled(&si.c, false, 0) {
                    if c.is_zero() {
                        scheme.remove(j);
                        scheme.remove(i);
                        return true;
                    }
                }
            }
            if let Some(m) = merged {
                if m.a.max_abs() <= cap
                    && m.b.max_abs() <= cap
                    && m.c.max_abs() <= cap
                {
                    scheme[j] = m;
                    scheme.remove(i);
                    return true;
                }
            }
        }
    }
    false
}

/// dyadic ratio x/y as (neg, exp) if it is +-2^k
fn dyadic_ratio(x: i128, y: i128) -> Option<(bool, i32)> {
    if x == 0 || y == 0 {
        return None;
    }
    let neg = (x < 0) != (y < 0);
    let (ax, ay) = (x.unsigned_abs(), y.unsigned_abs());
    let (big, small, sg) = if ax >= ay { (ax, ay, 1) } else { (ay, ax, -1) };
    if big % small != 0 {
        return None;
    }
    let q = big / small;
    if !q.is_power_of_two() {
        return None;
    }
    let k = q.trailing_zeros() as i32 * sg;
    if k.abs() > 20 { None } else { Some((neg, k)) }
}

/// targeted flip: for pair (i, j) sharing slot `slot`, find lambda
/// such that (transfer-slot factor of i) + lambda*(of j) becomes
/// PROPORTIONAL to the same-slot factor of some third summand m —
/// i.e. solve  f_i + lam f_j = mu f_m  (2 unknowns, 16 equations),
/// restricted to dyadic lam (mu arbitrary dyadic enforced by gauge).
/// Returns candidate (t1, lam) list.
fn coincidence_lams(
    scheme: &[Summand],
    i: usize,
    j: usize,
    slot: usize,
) -> Vec<(usize, (bool, i32), usize)> {
    let others: [usize; 2] = match slot {
        0 => [1, 2],
        1 => [0, 2],
        _ => [0, 1],
    };
    let mut out = Vec::new();
    for &t1 in &others {
        let fi = fac(&scheme[i], t1);
        let fj = fac(&scheme[j], t1);
        for m in 0..scheme.len() {
            if m == i || m == j {
                continue;
            }
            let fm = fac(&scheme[m], t1);
            // solve fi + lam fj = mu fm over the rationals via two
            // pivot coordinates, then verify all 16 exactly.
            // work at a common power-of-two scale.
            let e = fi.exp.min(fj.exp).min(fm.exp);
            let (si, sj, sm) = (
                (fi.exp - e) as u32,
                (fj.exp - e) as u32,
                (fm.exp - e) as u32,
            );
            if si > 30 || sj > 30 || sm > 30 {
                continue;
            }
            let gi = |k: usize| (fi.nums[k] as i128) << si;
            let gj = |k: usize| (fj.nums[k] as i128) << sj;
            let gm = |k: usize| (fm.nums[k] as i128) << sm;
            // find pivots: p with fm[p] != 0 or fj[p] != 0 giving a
            // 2x2 system in (lam, mu):  lam*gj - mu*gm = -gi
            let mut piv = None;
            'fp: for p in 0..16 {
                for q in p + 1..16 {
                    let det = gj(p) * (-gm(q)) - gj(q) * (-gm(p));
                    if det != 0 {
                        piv = Some((p, q, det));
                        break 'fp;
                    }
                }
            }
            let (p, q, det) = match piv {
                Some(x) => x,
                None => continue,
            };
            // Cramer for lam*gj(x) - mu*gm(x) = -gi(x) at x = p, q
            let nl = (-gi(p)) * (-gm(q)) - (-gi(q)) * (-gm(p));
            let nm = gj(p) * (-gi(q)) - gj(q) * (-gi(p));
            if nl == 0 || nm == 0 {
                continue; // degenerate: proportional already / lam 0
            }
            let lam = match dyadic_ratio(nl, det) {
                Some(l) => l,
                None => continue,
            };
            // verify all coordinates: det*(gi + lam*gj) == nm... use
            // exact check det*gi(x) + nl_scaled... simplest: check
            // det*(gi(x)) + (nl)*gj(x) - (nm)*gm(x) == 0 for all x
            if (0..16).all(|x| det * gi(x) + nl * gj(x) - nm * gm(x) == 0) {
                out.push((t1, lam, m));
            }
        }
    }
    out
}

fn scheme_hash(scheme: &[Summand]) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut keys: Vec<(&Vec16, &Vec16, &Vec16)> =
        scheme.iter().map(|t| (&t.a, &t.b, &t.c)).collect();
    keys.sort_by(|x, y| {
        (x.0.nums, x.0.exp, x.1.nums, x.1.exp, x.2.nums, x.2.exp).cmp(&(
            y.0.nums, y.0.exp, y.1.nums, y.1.exp, y.2.nums, y.2.exp,
        ))
    });
    let mut h = DefaultHasher::new();
    for k in keys {
        (k.0.nums, k.0.exp, k.1.nums, k.1.exp, k.2.nums, k.2.exp).hash(&mut h);
    }
    h.finish()
}

// ---------- seed loading (.sms triple) ----------
fn load_seed(dir: &str) -> Vec<Summand> {
    let parse = |p: &str| -> Vec<Vec<(usize, i64, i32)>> {
        // returns per-row sparse (col, num, exp) with value num*2^exp
        let txt = std::fs::read_to_string(p).expect(p);
        let mut dims = None;
        let mut rows: Vec<Vec<(usize, i64, i32)>> = Vec::new();
        for ln in txt.lines() {
            let ln = ln.trim();
            if ln.is_empty() || ln.starts_with('#') {
                continue;
            }
            let f: Vec<&str> = ln.split_whitespace().collect();
            if dims.is_none() {
                dims = Some((f[0].parse::<usize>().unwrap(),
                             f[1].parse::<usize>().unwrap()));
                rows = vec![Vec::new(); dims.unwrap().0];
                continue;
            }
            let (i, j): (usize, usize) =
                (f[0].parse().unwrap(), f[1].parse().unwrap());
            if i == 0 && j == 0 {
                break;
            }
            let v = f[2];
            let neg = v.starts_with('-');
            let v = v.trim_start_matches('-');
            let (num, exp) = if let Some((n, d)) = v.split_once('/') {
                let d: i64 = d.parse().unwrap();
                assert!(d.count_ones() == 1);
                (n.parse::<i64>().unwrap(), -(d.trailing_zeros() as i32))
            } else {
                (v.parse::<i64>().unwrap(), 0)
            };
            rows[i - 1].push((j - 1, if neg { -num } else { num }, exp));
        }
        rows
    };
    let mk = |sparse: &Vec<(usize, i64, i32)>| -> Vec16 {
        let emin = sparse.iter().map(|&(_, _, e)| e).min().unwrap_or(0);
        let mut nums = [0i64; 16];
        for &(j, n, e) in sparse {
            nums[j] = n << (e - emin) as u32;
        }
        Vec16 { nums, exp: emin }.normalize()
    };
    let l = parse(&format!("{dir}/L.sms"));
    let r = parse(&format!("{dir}/R.sms"));
    let p = parse(&format!("{dir}/P.sms")); // 16 x 48 -> transpose
    let mut pt: Vec<Vec<(usize, i64, i32)>> = vec![Vec::new(); 48];
    for (z, row) in p.iter().enumerate() {
        for &(i, n, e) in row {
            pt[i].push((z, n, e));
        }
    }
    (0..48)
        .map(|i| {
            Summand::gauge(mk(&l[i]), mk(&r[i]), mk(&pt[i])).expect("seed")
        })
        .collect()
}

/// v2: deterministic 2-ply coincidence pursuit at the seed.
/// For every (i, k, slot): split i against k, then look for a third
/// summand m reachable by TWO solved flips on the shared pair — one
/// aligning the split part with m in each free slot — and reduce.
/// Every hit is a constructively-derived rank-48 scheme (or lower!);
/// zero hits = a rigorous 1-split/2-flip rigidity certificate.
fn pursue(seed: &[Summand], cap: i64, outdir: &str) {
    use std::collections::HashSet;
    let seed_hash = scheme_hash(seed);
    let mut new48: HashSet<u64> = HashSet::new();
    let mut hits = 0u64;
    let mut alarms = 0u64;
    let mut saved = 0u32;
    let (mut n_split, mut n_c1, mut n_f1, mut n_c2) = (0u64, 0u64, 0u64, 0u64);
    for slot in 0..3usize {
        let others: [usize; 2] = match slot {
            0 => [1, 2],
            1 => [0, 2],
            _ => [0, 1],
        };
        for i in 0..48 {
            for k in 0..48 {
                if i == k {
                    continue;
                }
                // split i against k (mu = +1)
                let mut base = seed.to_vec();
                if !try_split(&mut base, i, k, slot, (false, 0), cap) {
                    continue;
                }
                n_split += 1;
                // ply 1 candidates on the shared pair (i, k)
                let cands1 = coincidence_lams(&base, i, k, slot);
                n_c1 += cands1.len() as u64;
                for &(t1, lam1, m) in &cands1 {
                    let mut s1 = base.clone();
                    let ok = if t1 == others[0] {
                        try_flip(&mut s1, i, k, slot, lam1, cap)
                    } else {
                        try_flip(&mut s1, k, i, slot, (!lam1.0, lam1.1), cap)
                    };
                    if !ok {
                        continue;
                    }
                    n_f1 += 1;
                    // ply 2: align the OTHER slot with the same m
                    let t2 = if t1 == others[0] { others[1] } else { others[0] };
                    let cands2 = coincidence_lams(&s1, i, k, slot);
                    n_c2 += cands2.len() as u64;
                    for &(t2c, lam2, m2) in &cands2 {
                        if t2c != t2 || m2 != m {
                            continue;
                        }
                        let mut s2 = s1.clone();
                        let ok2 = if t2 == others[0] {
                            try_flip(&mut s2, i, k, slot, lam2, cap)
                        } else {
                            try_flip(&mut s2, k, i, slot, (!lam2.0, lam2.1), cap)
                        };
                        if !ok2 {
                            continue;
                        }
                        hits += 1;
                        while try_reduce(&mut s2, cap * 4) {}
                        let rank = s2.len();
                        if rank < 48 {
                            if verify(&s2) {
                                alarms += 1;
                                let p = format!("{outdir}/RANK{rank}_pursue.txt");
                                dump(&s2, &p);
                                println!("*** RANK {rank} VERIFIED (pursue) -> {p} ***");
                            }
                        } else if rank == 48 {
                            let h = scheme_hash(&s2);
                            if h != seed_hash && verify(&s2) && new48.insert(h) {
                                if saved < 50 {
                                    let p = format!("{outdir}/new48_{saved}.txt");
                                    dump(&s2, &p);
                                    saved += 1;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    println!(
        "pursue funnel: {} splits, {} p1cands, {} p1flips, {} p2cands",
        n_split, n_c1, n_f1, n_c2
    );
    println!(
        "pursue: {} double-coplanar executions, {} NEW distinct rank-48          schemes ({} saved), {} sub-48 alarms",
        hits, new48.len(), saved, alarms
    );
}

/// v3: depth-D deterministic pursuit over ALL shared pairs of every
/// post-split state (includes the split-partner pair, whose transfers
/// open the s-slot coplanarity family).  Reduction checked at every
/// node.  Scope: shared pairs are detected by post-gauge equality —
/// complete for a/b slots (canon ⇒ proportional ⟺ equal), exact-equal
/// only for the scalar-carrying c slot.
fn pursue3(seed: &[Summand], cap: i64, depth_max: u32, outdir: &str) {
    use std::collections::HashSet;
    use std::sync::atomic::{AtomicU64, Ordering};
    let seed_hash = scheme_hash(seed);
    let n_nodes = AtomicU64::new(0);
    let n_new = AtomicU64::new(0);
    let n_alarm = AtomicU64::new(0);
    let roots: Vec<(usize, usize, usize)> = (0..3)
        .flat_map(|s| {
            (0..48).flat_map(move |i| {
                (0..48).filter(move |&k| k != i).map(move |k| (s, i, k))
            })
        })
        .collect();
    roots.par_iter().for_each(|&(slot, i, k)| {
        let mut base = seed.to_vec();
        if !try_split(&mut base, i, k, slot, (false, 0), cap) {
            return;
        }
        let mut seen: HashSet<u64> = HashSet::new();
        seen.insert(scheme_hash(&base));
        // stack DFS: (state, depth)
        let mut stack: Vec<(Vec<Summand>, u32)> = vec![(base, 0)];
        let mut budget = 60_000u64; // nodes per root
        while let Some((state, depth)) = stack.pop() {
            if budget == 0 {
                break;
            }
            budget -= 1;
            n_nodes.fetch_add(1, Ordering::Relaxed);
            // reduction probe
            let mut r = state.clone();
            while try_reduce(&mut r, cap * 4) {}
            if r.len() < 48 {
                if verify(&r) {
                    let a = n_alarm.fetch_add(1, Ordering::Relaxed);
                    let p = format!("{outdir}/RANK{}_p3_{}.txt", r.len(), a);
                    dump(&r, &p);
                    println!("*** RANK {} VERIFIED (pursue3) -> {} ***",
                             r.len(), p);
                }
            } else if r.len() == 48 {
                let h = scheme_hash(&r);
                if h != seed_hash && verify(&r) {
                    let a = n_new.fetch_add(1, Ordering::Relaxed);
                    if a < 40 {
                        let p = format!("{outdir}/new48_p3_{}.txt", a);
                        dump(&r, &p);
                        println!("NEW rank-48 scheme (pursue3) -> {p}");
                    }
                }
            }
            if depth >= depth_max {
                continue;
            }
            // all shared pairs, all slots
            let n = state.len();
            for ss in 0..3usize {
                for x in 0..n {
                    for y in x + 1..n {
                        if fac(&state[x], ss) != fac(&state[y], ss) {
                            continue;
                        }
                        let others: [usize; 2] = match ss {
                            0 => [1, 2],
                            1 => [0, 2],
                            _ => [0, 1],
                        };
                        for &(ord_x, ord_y) in &[(x, y), (y, x)] {
                            let cands =
                                coincidence_lams(&state, ord_x, ord_y, ss);
                            for &(t, lam, _m) in &cands {
                                let mut s2 = state.clone();
                                let ok = if t == others[0] {
                                    try_flip(&mut s2, ord_x, ord_y, ss,
                                             lam, cap)
                                } else {
                                    try_flip(&mut s2, ord_y, ord_x, ss,
                                             (!lam.0, lam.1), cap)
                                };
                                if !ok {
                                    continue;
                                }
                                let h = scheme_hash(&s2);
                                if seen.insert(h) {
                                    stack.push((s2, depth + 1));
                                }
                            }
                        }
                    }
                }
            }
        }
    });
    println!(
        "pursue3(depth {}): {} nodes explored, {} NEW rank-48, {} sub-48 alarms",
        depth_max,
        n_nodes.load(Ordering::Relaxed),
        n_new.load(Ordering::Relaxed),
        n_alarm.load(Ordering::Relaxed)
    );
}

    // closure of `root` under solved flips + reduction-continuations;
// returns closure states; records findings.
fn closure(
    root: Vec<Summand>,
    seed_hash: u64,
    cap: i64,
    max_seen: usize,
    outdir: &str,
    n_states: &AtomicU64,
    n_new48: &AtomicU64,
    n_sub48: &AtomicU64,
    saved: &AtomicU64,
) -> Vec<Vec<Summand>> {
    use std::collections::HashSet;
    let mut seen: HashSet<u64> = HashSet::new();
    let mut out: Vec<Vec<Summand>> = Vec::new();
    let mut stack = vec![root];
    while let Some(state) = stack.pop() {
        let h = scheme_hash(&state);
        if !seen.insert(h) {
            continue;
        }
        n_states.fetch_add(1, Ordering::Relaxed);
        // reduction probe -> continuation
        let mut r = state.clone();
        let mut reduced = false;
        while try_reduce(&mut r, cap * 4) {
            reduced = true;
        }
        if reduced {
            if r.len() < 48 {
                if verify(&r) {
                    let k = n_sub48.fetch_add(1, Ordering::Relaxed);
                    let p = format!("{outdir}/RANK{}_p4_{}.txt", r.len(), k);
                    dump(&r, &p);
                    println!("*** RANK {} VERIFIED (pursue4) -> {} ***",
                             r.len(), p);
                }
            } else if r.len() == 48 {
                let rh = scheme_hash(&r);
                if rh != seed_hash && verify(&r) {
                    let k = n_new48.fetch_add(1, Ordering::Relaxed);
                    if saved.load(Ordering::Relaxed) < 40 {
                        saved.fetch_add(1, Ordering::Relaxed);
                        let p = format!("{outdir}/new48_p4_{}.txt", k);
                        dump(&r, &p);
                        println!("NEW rank-48 (pursue4) -> {p}");
                    }
                }
            }
            // continue exploring from the reduced state
            if r.len() >= 48 && seen.len() < max_seen {
                stack.push(r);
            }
        }
        // solved-flip successors
        let n = state.len();
        for ss in 0..3usize {
            let others: [usize; 2] = match ss {
                0 => [1, 2],
                1 => [0, 2],
                _ => [0, 1],
            };
            for x in 0..n {
                for y in x + 1..n {
                    if fac(&state[x], ss) != fac(&state[y], ss) {
                        continue;
                    }
                    for &(oi, oj) in &[(x, y), (y, x)] {
                        for &(t, lam, _m) in
                            &coincidence_lams(&state, oi, oj, ss)
                        {
                            let mut s2 = state.clone();
                            let ok = if t == others[0] {
                                try_flip(&mut s2, oi, oj, ss, lam, cap)
                            } else {
                                try_flip(&mut s2, oj, oi, ss,
                                         (!lam.0, lam.1), cap)
                            };
                            if ok && seen.len() < max_seen {
                                stack.push(s2);
                            }
                        }
                    }
                }
            }
        }
        out.push(state);
    }
    out
}


/// v4: multi-split pursuit.  From each state: close under solved
/// flips; PROBE reductions and CONTINUE exploring from reduced states
/// (reductions are first-class moves — the 50 -> 49' -> 48' path);
/// while split budget remains, recurse into every split of every
/// closure state.  Exhaustive at split budget 2 (~54M roots, tiny
/// closures); findings saved + verified.
fn pursue4(seed: &[Summand], cap: i64, splits: u32, outdir: &str) {
    use std::collections::HashSet;
    use std::sync::atomic::{AtomicU64, Ordering};
    let seed_hash = scheme_hash(seed);
    let n_states = AtomicU64::new(0);
    let n_new48 = AtomicU64::new(0);
    let n_sub48 = AtomicU64::new(0);
    let saved = AtomicU64::new(0);

    // (closure lifted to a free fn below)

    // recursive split levels
    fn level(
        states: Vec<Vec<Summand>>,
        budget: u32,
        seed_hash: u64,
        cap: i64,
        outdir: &str,
        n_states: &AtomicU64,
        n_new48: &AtomicU64,
        n_sub48: &AtomicU64,
        saved: &AtomicU64,
    ) {
        if budget == 0 {
            return;
        }
        for st in states {
            let n = st.len();
            for ss in 0..3usize {
                for i in 0..n {
                    for k in 0..n {
                        if i == k {
                            continue;
                        }
                        let mut base = st.clone();
                        if !try_split(&mut base, i, k, ss, (false, 0), cap) {
                            continue;
                        }
                        let cl = closure(base, seed_hash, cap, 20_000, outdir,
                                         n_states, n_new48, n_sub48, saved);
                        level(cl, budget - 1, seed_hash, cap, outdir,
                              n_states, n_new48, n_sub48, saved);
                    }
                }
            }
        }
    }

    // first level parallel over root splits of the seed
    let roots: Vec<(usize, usize, usize)> = (0..3)
        .flat_map(|s| {
            (0..48).flat_map(move |i| {
                (0..48).filter(move |&k| k != i).map(move |k| (s, i, k))
            })
        })
        .collect();
    roots.par_iter().for_each(|&(ss, i, k)| {
        let mut base = seed.to_vec();
        if !try_split(&mut base, i, k, ss, (false, 0), cap) {
            return;
        }
        let cl = closure(base, seed_hash, cap, 20_000, outdir,
                         &n_states, &n_new48, &n_sub48, &saved);
        level(cl, splits - 1, seed_hash, cap, outdir,
              &n_states, &n_new48, &n_sub48, &saved);
    });
    println!(
        "pursue4(splits {}): {} states, {} NEW rank-48, {} sub-48 alarms",
        splits,
        n_states.load(Ordering::Relaxed),
        n_new48.load(Ordering::Relaxed),
        n_sub48.load(Ordering::Relaxed)
    );
}

/// export the full 1-split solved-move component as a JSON graph:
/// full per-state metrics: (shared, coinc, copl, maxc, nearmiss)
fn state_metrics(st: &Vec<Summand>) -> (usize, usize, usize, i64, usize) {
    let n = st.len();
    let mut shared = 0usize;
    let mut coinc = 0usize;
    let mut nearmiss = 0usize;
    for ss in 0..3usize {
        for x in 0..n {
            for y in x + 1..n {
                if fac(&st[x], ss) == fac(&st[y], ss) {
                    shared += 1;
                    let c1 = coincidence_lams(st, x, y, ss);
                    let c2 = coincidence_lams(st, y, x, ss);
                    coinc += c1.len() + c2.len();
                    // near-miss: distinct m's reachable in ply 1
                    let mut ms: Vec<usize> =
                        c1.iter().chain(c2.iter()).map(|&(_, _, m)| m).collect();
                    ms.sort_unstable();
                    ms.dedup();
                    nearmiss += ms.len();
                }
            }
        }
    }
    // coplanar triples (rank<=2 factor triples), a-slot only
    let mut copl = 0usize;
    for x in 0..n {
        for y in x + 1..n {
            for z in y + 1..n {
                let e = fac(&st[x], 0).exp
                    .min(fac(&st[y], 0).exp)
                    .min(fac(&st[z], 0).exp);
                let g = |v: &Vec16, k: usize| -> i128 {
                    (v.nums[k] as i128) << (v.exp - e) as u32
                };
                let (vx, vy, vz) =
                    (fac(&st[x], 0), fac(&st[y], 0), fac(&st[z], 0));
                // coplanar iff all 3x3 minors over the 16 coords vanish
                let mut ok = true;
                'mn: for p in 0..16 {
                    for q in (p + 1)..16 {
                        for r in (q + 1)..16 {
                            let d = g(vx, p) * (g(vy, q) * g(vz, r) - g(vy, r) * g(vz, q))
                                - g(vy, p) * (g(vx, q) * g(vz, r) - g(vx, r) * g(vz, q))
                                + g(vz, p) * (g(vx, q) * g(vy, r) - g(vx, r) * g(vy, q));
                            if d != 0 {
                                ok = false;
                                break 'mn;
                            }
                        }
                    }
                }
                if ok {
                    copl += 1;
                }
            }
        }
    }
    let maxc = st.iter()
        .map(|t| t.a.max_abs().max(t.b.max_abs()).max(t.c.max_abs()))
        .max()
        .unwrap_or(0);
    (shared, coinc, copl, maxc, nearmiss)
}

const SLOT: [&str; 3] = ["a", "b", "c"];

fn lam_str(l: (bool, i32)) -> String {
    let (neg, k) = l;
    let v = if k >= 0 {
        (1i64 << k).to_string()
    } else {
        format!("1/{}", 1i64 << (-k) as u32)
    };
    if neg { format!("-{v}") } else { v }
}

/// dyadic Vec16 as a sparse combination of 4x4 matrix units e_rc
fn pretty_v16(v: &Vec16) -> String {
    let mut out = String::new();
    for k in 0..16 {
        let n = v.nums[k];
        if n == 0 {
            continue;
        }
        let (r, c) = (k / 4 + 1, k % 4 + 1);
        let (num, den) = if v.exp >= 0 {
            ((n as i128) << v.exp as u32, 1i128)
        } else {
            let sh = (-v.exp) as u32;
            let tz = n.trailing_zeros().min(sh);
            ((n >> tz) as i128, 1i128 << (sh - tz))
        };
        let mag = if den == 1 {
            format!("{}", num.abs())
        } else {
            format!("{}/{}", num.abs(), den)
        };
        let sign = if num < 0 { "-" } else { "+" };
        if mag == "1" {
            out += &format!("{sign}e{r}{c} ");
        } else {
            out += &format!("{sign}{mag}e{r}{c} ");
        }
    }
    let s = out.trim_end();
    s.strip_prefix('+').unwrap_or(s).to_string()
}

/// worked example for the paper appendix: find a split whose flip
/// component contains nearmiss-2, nearmiss-1, nearmiss-0 and copl-109
/// states, then print a single walk visiting all four with the full
/// move algebra (shared factor, solved lambda, target, rewrites).
fn worked(seed: &[Summand], cap: i64) {
    use std::collections::{HashMap, HashSet, VecDeque};
    let pm = |st: &Vec<Summand>| state_metrics(st);
    let (sh, co, cp, mx, nm) = pm(&seed.to_vec());
    println!("SEED  rank 48  shared {sh}  coinc {co}  nearmiss {nm}  copl {cp}  maxc {mx}");

    // all solved flips out of st, with human-readable move descriptions
    let expand = |st: &Vec<Summand>| -> Vec<(String, Vec<Summand>)> {
        let mut out = Vec::new();
        let n = st.len();
        for s2 in 0..3usize {
            let others: [usize; 2] = match s2 {
                0 => [1, 2],
                1 => [0, 2],
                _ => [0, 1],
            };
            for x in 0..n {
                for y in x + 1..n {
                    if fac(&st[x], s2) != fac(&st[y], s2) {
                        continue;
                    }
                    for &(oi, oj) in &[(x, y), (y, x)] {
                        for &(t, lam, m) in &coincidence_lams(st, oi, oj, s2) {
                            let mut c = st.clone();
                            let ok = if t == others[0] {
                                try_flip(&mut c, oi, oj, s2, lam, cap)
                            } else {
                                try_flip(&mut c, oj, oi, s2, (!lam.0, lam.1), cap)
                            };
                            if !ok {
                                continue;
                            }
                            let tc = if t == others[0] { others[1] } else { others[0] };
                            let desc = format!(
                                "flip on pair ({oi},{oj}), shared {}-factor [{}]\n  solve {}_{oi} + λ·{}_{oj} ∝ {}_{m}:  λ = {}\n  {}_{oi}: {}\n     →   {}   (∝ {}_{m} = {})\n  comp {}_{oj}: {}  →  {}",
                                SLOT[s2], pretty_v16(fac(&st[oi], s2)),
                                SLOT[t], SLOT[t], SLOT[t], lam_str(lam),
                                SLOT[t], pretty_v16(fac(&st[oi], t)),
                                pretty_v16(fac(&c[oi], t)),
                                SLOT[t], pretty_v16(fac(&st[m], t)),
                                SLOT[tc], pretty_v16(fac(&st[oj], tc)),
                                pretty_v16(fac(&c[oj], tc))
                            );
                            out.push((desc, c));
                        }
                    }
                }
            }
        }
        out
    };

    // shortest solved-flip path from `from` to the first state with `want`
    let bfs_leg = |from: &Vec<Summand>,
                   want: &dyn Fn(&Vec<Summand>) -> bool|
     -> Option<Vec<(String, Vec<Summand>)>> {
        let fh = scheme_hash(from);
        let mut par: HashMap<u64, (u64, String, Vec<Summand>)> = HashMap::new();
        let mut seen: HashSet<u64> = HashSet::new();
        seen.insert(fh);
        let mut q = VecDeque::new();
        q.push_back(from.clone());
        let mut hit: Option<u64> = None;
        'b: while let Some(st) = q.pop_front() {
            if seen.len() > 400 {
                break;
            }
            let h = scheme_hash(&st);
            for (d, c) in expand(&st) {
                let ch = scheme_hash(&c);
                if !seen.insert(ch) {
                    continue;
                }
                par.insert(ch, (h, d, c.clone()));
                if want(&c) {
                    hit = Some(ch);
                    break 'b;
                }
                q.push_back(c);
            }
        }
        let mut hh = hit?;
        let mut legs = Vec::new();
        while hh != fh {
            let (ph, d, s) = par.get(&hh).unwrap().clone();
            legs.push((d, s));
            hh = ph;
        }
        legs.reverse();
        Some(legs)
    };

    'outer: for ss in 0..3usize {
        for i in 0..48usize {
            for k in 0..48usize {
                if i == k {
                    continue;
                }
                let mut root = seed.to_vec();
                if !try_split(&mut root, i, k, ss, (false, 0), cap) {
                    continue;
                }
                // attempt the full milestone walk; on any failed leg,
                // move on to the next split candidate
                let cats: Vec<(&str, Box<dyn Fn(&Vec<Summand>) -> bool>)> = vec![
                    ("nearmiss 2", Box::new(|s: &Vec<Summand>| state_metrics(s).4 == 2)),
                    ("copl 109", Box::new(|s: &Vec<Summand>| state_metrics(s).2 == 109)),
                    ("nearmiss 1", Box::new(|s: &Vec<Summand>| state_metrics(s).4 == 1)),
                    ("nearmiss 0 (flip sink)",
                     Box::new(|s: &Vec<Summand>| state_metrics(s).4 == 0)),
                ];
                let mut walk: Vec<String> = Vec::new();
                let mut cur = root.clone();
                let mut stepno = 0usize;
                let mut okall = true;
                for (label, want) in &cats {
                    if want(&cur) {
                        walk.push(format!("[{label}] — current state already qualifies"));
                        continue;
                    }
                    match bfs_leg(&cur, want.as_ref()) {
                        None => {
                            okall = false;
                            break;
                        }
                        Some(legs) => {
                            walk.push(format!("-- leg to {label}: {} step(s) --", legs.len()));
                            for (d, s) in legs {
                                stepno += 1;
                                let (sh, co, cp, mx, nm) = pm(&s);
                                walk.push(format!("step {stepno}: {d}"));
                                walk.push(format!(
                                    "  state: shared {sh}  coinc {co}  nearmiss {nm}  copl {cp}  maxc {mx}"
                                ));
                                cur = s;
                            }
                        }
                    }
                }
                if !okall {
                    continue;
                }
                // success: print split detail + the walk
                println!("\nSPLIT: summand {i} against summand {k} in slot {} (μ = 1):", SLOT[ss]);
                println!("  {}_{i} = {}", SLOT[ss], pretty_v16(fac(&seed[i], ss)));
                println!("  {}_{k} = {}", SLOT[ss], pretty_v16(fac(&seed[k], ss)));
                println!("  summand {i} := ({}_{k}) ⊗ (rest of {i})  +  ({}_{i} − {}_{k}) ⊗ (rest of {i})",
                         SLOT[ss], SLOT[ss], SLOT[ss]);
                println!("  new summand 48 carries the remainder factor: {}",
                         pretty_v16(fac(&root[48], ss)));
                let (sh, co, cp, mx, nm) = pm(&root);
                println!("  ROOT  rank 49  shared {sh}  coinc {co}  nearmiss {nm}  copl {cp}  maxc {mx}");
                for line in walk {
                    println!("{line}");
                }
                println!("\nwalk complete: 1 split + {stepno} solved flips");
                break 'outer;
            }
        }
    }
}

/// nodes (rank, shared pairs, coincidence count, coplanar triples,
/// max coefficient, near-miss count) + typed edges.
fn graph_export(seed: &[Summand], cap: i64, path: &str) {
    use std::collections::HashMap;
    let seed_hash = scheme_hash(seed);
    let mut ids: HashMap<u64, usize> = HashMap::new();
    let mut nodes: Vec<String> = Vec::new();
    let mut edges: Vec<String> = Vec::new();
    let mut stack: Vec<(Vec<Summand>, usize)> = Vec::new();

    let mut metrics =
        |st: &Vec<Summand>| -> (usize, usize, usize, i64, usize) { state_metrics(st) };

    let mut add_node = |st: &Vec<Summand>,
                        ids: &mut HashMap<u64, usize>,
                        nodes: &mut Vec<String>,
                        stack: &mut Vec<(Vec<Summand>, usize)>,
                        metrics: &mut dyn FnMut(&Vec<Summand>) -> (usize, usize, usize, i64, usize)|
     -> (usize, bool) {
        let h = scheme_hash(st);
        if let Some(&id) = ids.get(&h) {
            return (id, false);
        }
        let id = nodes.len();
        ids.insert(h, id);
        let (sh, co, cp, mx, nm) = metrics(st);
        nodes.push(format!(
            "{{\"id\":{},\"rank\":{},\"shared\":{},\"coinc\":{},\"copl\":{},\"maxc\":{},\"nearmiss\":{},\"isSeed\":{}}}",
            id, st.len(), sh, co, cp, mx, nm,
            scheme_hash(st) == seed_hash
        ));
        stack.push((st.clone(), id));
        (id, true)
    };

    let (seed_id, _) = add_node(&seed.to_vec(), &mut ids, &mut nodes, &mut stack, &mut metrics);
    // root splits
    for ss in 0..3usize {
        for i in 0..48 {
            for k in 0..48 {
                if i == k {
                    continue;
                }
                let mut base = seed.to_vec();
                if try_split(&mut base, i, k, ss, (false, 0), cap) {
                    let (id, _) = add_node(&base, &mut ids, &mut nodes, &mut stack, &mut metrics);
                    edges.push(format!(
                        "{{\"s\":{},\"t\":{},\"ty\":\"split\"}}",
                        seed_id, id
                    ));
                }
            }
        }
    }
    // closure under solved flips + reduction edges
    let mut qi = 0usize;
    while qi < stack.len() {
        let (st, sid) = stack[qi].clone();
        qi += 1;
        if sid == seed_id {
            continue;
        }
        // reduction edge
        let mut r = st.clone();
        let mut reduced = false;
        while try_reduce(&mut r, cap * 4) {
            reduced = true;
        }
        if reduced {
            let (rid, _) = add_node(&r, &mut ids, &mut nodes, &mut stack, &mut metrics);
            edges.push(format!(
                "{{\"s\":{},\"t\":{},\"ty\":\"reduce\"}}",
                sid, rid
            ));
        }
        // solved flips
        let n = st.len();
        for ss in 0..3usize {
            let others: [usize; 2] = match ss {
                0 => [1, 2],
                1 => [0, 2],
                _ => [0, 1],
            };
            for x in 0..n {
                for y in x + 1..n {
                    if fac(&st[x], ss) != fac(&st[y], ss) {
                        continue;
                    }
                    for &(oi, oj) in &[(x, y), (y, x)] {
                        for &(t, lam, _m) in &coincidence_lams(&st, oi, oj, ss) {
                            let mut s2 = st.clone();
                            let ok = if t == others[0] {
                                try_flip(&mut s2, oi, oj, ss, lam, cap)
                            } else {
                                try_flip(&mut s2, oj, oi, ss, (!lam.0, lam.1), cap)
                            };
                            if ok {
                                let (id2, _) = add_node(&s2, &mut ids, &mut nodes, &mut stack, &mut metrics);
                                edges.push(format!(
                                    "{{\"s\":{},\"t\":{},\"ty\":\"flip\"}}",
                                    sid, id2
                                ));
                            }
                        }
                    }
                }
            }
        }
    }
    let json = format!(
        "{{\"nodes\":[{}],\"edges\":[{}]}}",
        nodes.join(","),
        edges.join(",")
    );
    std::fs::write(path, json).unwrap();
    println!("graph: {} nodes, {} edges -> {}", nodes.len(), edges.len(), path);
}

/// light nearmiss metric: distinct ply-1 targets across shared pairs
fn nearmiss_of(st: &[Summand]) -> usize {
    let n = st.len();
    let mut total = 0usize;
    for ss in 0..3usize {
        for x in 0..n {
            for y in x + 1..n {
                if fac(&st[x], ss) != fac(&st[y], ss) {
                    continue;
                }
                let mut ms: Vec<usize> = coincidence_lams(st, x, y, ss)
                    .iter()
                    .chain(coincidence_lams(st, y, x, ss).iter())
                    .map(|&(_, _, m)| m)
                    .collect();
                ms.sort_unstable();
                ms.dedup();
                total += ms.len();
            }
        }
    }
    total
}

/// Random-walk nearmiss baseline — the control for the chase gradient.
/// For each depth k in 1..=maxk: N unguided random k-split walks from
/// the seed (uniform (slot, i, partner), mu = 1, exactly as pursue6
/// samples splits), then nearmiss_of the raw endpoint (rank 48+k;
/// chase level L states carry L+1 splits, so level L <-> k = L+1).
/// Distinguishes "the beam concentrates real structure" from
/// "nearmiss inflates mechanically with rank".  top1500 = mean of the
/// 1500 best samples: what one-shot selection (no guidance) achieves.
fn nmrand(seed: &[Summand], cap: i64, maxk: usize, n: usize) {
    println!("nmrand control: {n} unguided walks per depth, depths 1..={maxk}");
    println!("{:>3} {:>5} {:>6} {:>8} {:>5} {:>5} {:>5} {:>5} {:>6} {:>8}",
             "k", "rank", "level", "mean", "p50", "p90", "p99", "max",
             "pos%", "top1500");
    for k in 1..=maxk {
        let mut nms: Vec<usize> = (0..n)
            .into_par_iter()
            .filter_map(|w| {
                let mut rng = Rng((0xC0FFEE_u64
                    ^ ((k as u64) << 32)
                    ^ (w as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15)) | 1);
                let mut st = seed.to_vec();
                let mut applied = 0usize;
                for _try in 0..100_000 {
                    if applied == k {
                        break;
                    }
                    let (ss, i, kk) =
                        (rng.below(3), rng.below(st.len()), rng.below(st.len()));
                    if i == kk {
                        continue;
                    }
                    if try_split(&mut st, i, kk, ss, (false, 0), cap) {
                        applied += 1;
                    }
                }
                if applied < k {
                    return None;
                }
                Some(nearmiss_of(&st))
            })
            .collect();
        nms.sort_unstable();
        let cnt = nms.len();
        if cnt == 0 {
            println!("{k:>3} {:>5} {:>6} (no completed walks)", 48 + k, k - 1);
            continue;
        }
        let mean = nms.iter().sum::<usize>() as f64 / cnt as f64;
        let q = |p: f64| nms[((cnt - 1) as f64 * p) as usize];
        let pos = nms.iter().filter(|&&x| x > 0).count() as f64
            / cnt as f64 * 100.0;
        let top = 1500.min(cnt);
        let top_mean = nms[cnt - top..].iter().sum::<usize>() as f64
            / top as f64;
        println!(
            "{k:>3} {:>5} {:>6} {mean:>8.2} {:>5} {:>5} {:>5} {:>5} {pos:>5.1}% {top_mean:>8.2}",
            48 + k, k as i64 - 1, q(0.5), q(0.9), q(0.99),
            nms[cnt - 1]
        );
    }
}

/// v5: instrumented, sampled, gradient-guided 2-split pursuit.
/// Parents = the 1-split component states ordered fringe-first
/// (nearmiss desc); per parent, sample K random second splits (K = 0
/// means all); each root closed under solved flips with reduction
/// continuations.  Ticker + global state budget + nearmiss-depth
/// tracking (the empirical gradient: does depth-2 exceed 2?).
fn pursue5(seed: &[Summand], cap: i64, k_sample: usize, budget: u64,
           fringe_only: bool, resume: bool, outdir: &str) {
    use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
    let seed_hash = scheme_hash(seed);
    // collect the 1-split component (deduped states)
    let mut seen = std::collections::HashSet::new();
    let mut parents: Vec<Vec<Summand>> = Vec::new();
    for ss in 0..3usize {
        for i in 0..48 {
            for k in 0..48 {
                if i == k {
                    continue;
                }
                let mut base = seed.to_vec();
                if !try_split(&mut base, i, k, ss, (false, 0), cap) {
                    continue;
                }
                // light closure (flips only) to gather states
                let mut stack = vec![base];
                while let Some(st) = stack.pop() {
                    if !seen.insert(scheme_hash(&st)) {
                        continue;
                    }
                    let n = st.len();
                    for s2 in 0..3usize {
                        let others: [usize; 2] = match s2 {
                            0 => [1, 2],
                            1 => [0, 2],
                            _ => [0, 1],
                        };
                        for x in 0..n {
                            for y in x + 1..n {
                                if fac(&st[x], s2) != fac(&st[y], s2) {
                                    continue;
                                }
                                for &(oi, oj) in &[(x, y), (y, x)] {
                                    for &(t, lam, _m) in
                                        &coincidence_lams(&st, oi, oj, s2)
                                    {
                                        let mut c = st.clone();
                                        let ok = if t == others[0] {
                                            try_flip(&mut c, oi, oj, s2, lam, cap)
                                        } else {
                                            try_flip(&mut c, oj, oi, s2,
                                                     (!lam.0, lam.1), cap)
                                        };
                                        if ok {
                                            stack.push(c);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    parents.push(st);
                }
            }
        }
    }
    // gradient ordering: fringe first
    let mut scored: Vec<(usize, usize)> = parents
        .iter()
        .enumerate()
        .map(|(i, st)| (nearmiss_of(st), i))
        .collect();
    scored.sort_by(|a, b| b.0.cmp(&a.0));
    if fringe_only {
        scored.retain(|&(nm, _)| nm > 0);
        println!("fringe-only: {} parents retained", scored.len());
    }
    println!(
        "pursue5: {} parents; nearmiss>0 parents: {}; sampling {} splits/parent, budget {}",
        parents.len(),
        scored.iter().filter(|(nm, _)| *nm > 0).count(),
        if k_sample == 0 { "ALL".to_string() } else { k_sample.to_string() },
        budget
    );
    // sound resume: parents complete in work-stealing (scattered) order,
    // so a budget stop leaves a non-prefix done-set.  Log each completed
    // parent index (stable across runs: enumeration + stable sort are
    // deterministic); --resume skips exactly the logged ones.
    let done_path = format!("{outdir}/fringe_done.txt");
    let mut done_set = std::collections::HashSet::new();
    if resume {
        if let Ok(txt) = std::fs::read_to_string(&done_path) {
            for line in txt.lines() {
                if let Ok(pi) = line.trim().parse::<usize>() {
                    done_set.insert(pi);
                }
            }
        }
        println!("resume: {} parents already logged done", done_set.len());
    }
    let done_log = Mutex::new(
        std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(&done_path)
            .unwrap(),
    );
    let n_states = AtomicU64::new(0);
    let n_new48 = AtomicU64::new(0);
    let n_sub48 = AtomicU64::new(0);
    let saved = AtomicU64::new(0);
    let done = AtomicUsize::new(0);
    let max_nm2 = AtomicUsize::new(0);
    let order: Vec<usize> = scored
        .iter()
        .map(|&(_, i)| i)
        .filter(|pi| !done_set.contains(pi))
        .collect();
    println!("pursue5: {} parents to process this run", order.len());
    order.par_iter().for_each(|&pi| {
        if n_states.load(Ordering::Relaxed) > budget {
            return;
        }
        let st = &parents[pi];
        let n = st.len();
        let mut rng = Rng(0x1234_5678u64 ^ (pi as u64 * 0x9e37_79b9 + 1));
        let mut picks: Vec<(usize, usize, usize)> = Vec::new();
        if k_sample == 0 {
            for ss in 0..3 {
                for i in 0..n {
                    for k in 0..n {
                        if i != k {
                            picks.push((ss, i, k));
                        }
                    }
                }
            }
        } else {
            for _ in 0..k_sample {
                picks.push((rng.below(3), rng.below(n), rng.below(n)));
            }
        }
        for (ss, i, k) in picks {
            if i == k {
                continue;
            }
            let mut base = st.clone();
            if !try_split(&mut base, i, k, ss, (false, 0), cap) {
                continue;
            }
            let cl = closure(base, seed_hash, cap, 20_000, outdir,
                             &n_states, &n_new48, &n_sub48, &saved);
            // gradient probe: sample nearmiss at depth 2
            if let Some(deep) = cl.first() {
                let nm = nearmiss_of(deep);
                let prev = max_nm2.load(Ordering::Relaxed);
                if nm > prev {
                    max_nm2.store(nm, Ordering::Relaxed);
                    println!("depth-2 nearmiss = {nm} (new max)");
                }
            }
        }
        {
            use std::io::Write;
            let mut f = done_log.lock().unwrap();
            writeln!(f, "{pi}").ok();
            f.flush().ok();
        }
        let d = done.fetch_add(1, Ordering::Relaxed) + 1;
        if d % 200 == 0 {
            println!(
                "[tick] parents {}/{}  states {}  new48 {}  sub48 {}  max-nm2 {}",
                d,
                order.len(),
                n_states.load(Ordering::Relaxed),
                n_new48.load(Ordering::Relaxed),
                n_sub48.load(Ordering::Relaxed),
                max_nm2.load(Ordering::Relaxed)
            );
        }
    });
    println!(
        "pursue5 done: {} states, {} NEW rank-48, {} sub-48, max depth-2 nearmiss {}",
        n_states.load(Ordering::Relaxed),
        n_new48.load(Ordering::Relaxed),
        n_sub48.load(Ordering::Relaxed),
        max_nm2.load(Ordering::Relaxed)
    );
}

/// parse one dumped Vec16: "([n1, n2, ...], exp)"
fn parse_v16(s: &str) -> Option<Vec16> {
    let s = s.trim().strip_prefix('(')?.strip_suffix(')')?;
    let (l, r) = s.rsplit_once("], ")?;
    let mut nums = [0i64; 16];
    for (i, tok) in l.strip_prefix('[')?.split(',').enumerate() {
        if i >= 16 {
            return None;
        }
        nums[i] = tok.trim().parse().ok()?;
    }
    Some(Vec16 { nums, exp: r.trim().parse().ok()? })
}

/// parse a chase_frontier_L*.txt dump back into schemes.  Format per
/// state: optional "nearmiss N" line, one "va | vb | vc" line per
/// summand, "---" terminator.  Panics loudly on any malformed line.
fn parse_frontier(path: &str) -> Vec<Vec<Summand>> {
    let txt = std::fs::read_to_string(path).expect("read resume file");
    let mut out = Vec::new();
    for block in txt.split("---\n") {
        let mut st: Vec<Summand> = Vec::new();
        for line in block.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with("nearmiss") {
                continue;
            }
            let mut p = line.split(" | ");
            let (a, b, c) = (|| {
                Some((parse_v16(p.next()?)?, parse_v16(p.next()?)?,
                      parse_v16(p.next()?)?))
            })().unwrap_or_else(|| panic!("bad frontier line: {line}"));
            st.push(Summand::gauge(a, b, c).expect("gauge on resumed summand"));
        }
        if !st.is_empty() {
            out.push(st);
        }
    }
    out
}

/// v6: gradient chase — best-first beam on nearmiss across split
/// depths.  frontier := fringe parents; each level: sample K splits
/// per frontier state, close under solved flips, score every closure
/// state by nearmiss, keep the global top-B; repeat to depth D.
fn pursue6(seed: &[Summand], cap: i64, beam: usize, k_sample: usize,
           depth: u32, budget: u64, outdir: &str,
           resume: Option<&str>, start_level: u32) {
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::sync::Mutex;
    let seed_hash = scheme_hash(seed);
    let mut chase_seen = std::collections::HashSet::new();
    let mut frontier: Vec<(usize, Vec<Summand>)> = Vec::new();
    if let Some(path) = resume {
        // resume from a persisted frontier dump: parse, exact-verify,
        // re-score; historical cross-level dedup is not recoverable, so
        // old states may be re-visited (wasted work, never wrong answers)
        for st in parse_frontier(path) {
            assert!(verify(&st), "resumed state fails exact verification");
            chase_seen.insert(scheme_hash(&st));
            frontier.push((nearmiss_of(&st), st));
        }
        frontier.sort_by(|a, b| b.0.cmp(&a.0));
        println!("chase resume: {} verified states from {}; continuing at level {}",
                 frontier.len(), path, start_level + 1);
    } else {
        // level-0 frontier: fringe parents (nearmiss > 0)
        let mut seen = std::collections::HashSet::new();
        for ss in 0..3usize {
            for i in 0..48 {
                for k in 0..48 {
                    if i == k {
                        continue;
                    }
                    let mut base = seed.to_vec();
                    if !try_split(&mut base, i, k, ss, (false, 0), cap) {
                        continue;
                    }
                    if seen.insert(scheme_hash(&base)) {
                        let nm = nearmiss_of(&base);
                        if nm > 0 {
                            frontier.push((nm, base));
                        }
                    }
                }
            }
        }
        frontier.sort_by(|a, b| b.0.cmp(&a.0));
        frontier.truncate(beam);
        println!("chase: level 0 frontier {} (nearmiss max {})",
                 frontier.len(),
                 frontier.first().map(|x| x.0).unwrap_or(0));
    }
    let n_states = AtomicU64::new(0);
    let n_new48 = AtomicU64::new(0);
    let n_sub48 = AtomicU64::new(0);
    let saved = AtomicU64::new(0);
    for level in (start_level + 1)..=depth {
        if n_states.load(Ordering::Relaxed) > budget {
            println!("budget exhausted");
            break;
        }
        let next: Mutex<Vec<(usize, Vec<Summand>)>> = Mutex::new(Vec::new());
        frontier.par_iter().for_each(|(_, st)| {
            let mut rng = Rng(scheme_hash(st) | 1);
            let n = st.len();
            for _ in 0..k_sample {
                let (ss, i, k) = (rng.below(3), rng.below(n), rng.below(n));
                if i == k {
                    continue;
                }
                let mut base = st.clone();
                if !try_split(&mut base, i, k, ss, (false, 0), cap) {
                    continue;
                }
                let cl = closure(base, seed_hash, cap, 150, outdir,
                                 &n_states, &n_new48, &n_sub48, &saved);
                // two-stage scoring: cheap shared-pair count for
                // all closure states, full nearmiss only for the top 6
                let mut pre: Vec<(usize, Vec<Summand>)> = cl
                    .into_iter()
                    .map(|c| {
                        let n = c.len();
                        let mut sh = 0usize;
                        for ss in 0..3usize {
                            for x in 0..n {
                                for y in x + 1..n {
                                    if fac(&c[x], ss) == fac(&c[y], ss) {
                                        sh += 1;
                                    }
                                }
                            }
                        }
                        (sh, c)
                    })
                    .filter(|(sh, _)| *sh > 0)
                    .collect();
                pre.sort_by(|a, b| b.0.cmp(&a.0));
                pre.truncate(6);
                let local: Vec<(usize, Vec<Summand>)> = pre
                    .into_iter()
                    .map(|(_, c)| (nearmiss_of(&c), c))
                    .filter(|(nm, _)| *nm > 0)
                    .collect();
                next.lock().unwrap().extend(local);
            }
        });
        let mut nx = next.into_inner().unwrap();
        nx.sort_by(|a, b| b.0.cmp(&a.0));
        // dedup by hash keeping best-first order, across ALL levels
        nx.retain(|(_, st)| chase_seen.insert(scheme_hash(st)));
        nx.truncate(beam);
        // persist the FULL frontier: --resume6 restarts losslessly from
        // this file (H6: the resume set must be the complete identity
        // list, not a sample — top-50 dumps cost us a lossy resume once)
        {
            let mut txt = String::new();
            for (nm, st) in nx.iter() {
                txt += &format!("nearmiss {nm}\n");
                for t in st {
                    txt += &format!("{:?} | {:?} | {:?}\n",
                                    (t.a.nums, t.a.exp),
                                    (t.b.nums, t.b.exp),
                                    (t.c.nums, t.c.exp));
                }
                txt += "---\n";
            }
            std::fs::write(format!("{outdir}/chase_frontier_L{level}.txt"),
                           txt).ok();
        }
        let mx = nx.first().map(|x| x.0).unwrap_or(0);
        let mean: f64 = if nx.is_empty() { 0.0 } else {
            nx.iter().map(|x| x.0 as f64).sum::<f64>() / nx.len() as f64
        };
        println!(
            "chase level {}: frontier {}  nearmiss max {}  mean {:.1}               states {}  new48 {}  sub48 {}",
            level, nx.len(), mx, mean,
            n_states.load(Ordering::Relaxed),
            n_new48.load(Ordering::Relaxed),
            n_sub48.load(Ordering::Relaxed)
        );
        if nx.is_empty() {
            break;
        }
        frontier = nx;
    }
    println!(
        "chase done: {} states, {} NEW rank-48, {} sub-48",
        n_states.load(Ordering::Relaxed),
        n_new48.load(Ordering::Relaxed),
        n_sub48.load(Ordering::Relaxed)
    );
}

fn dump(s: &[Summand], path: &str) {
    let mut txt = String::new();
    for t in s {
        txt += &format!("{:?} | {:?} | {:?}\n",
                        (t.a.nums, t.a.exp),
                        (t.b.nums, t.b.exp),
                        (t.c.nums, t.c.exp));
    }
    std::fs::write(path, txt).ok();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |flag: &str, default: i64| -> i64 {
        args.iter()
            .position(|a| a == flag)
            .and_then(|i| args.get(i + 1))
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    };
    let dir = args
        .iter()
        .position(|a| a == "--dir")
        .and_then(|i| args.get(i + 1).cloned())
        .unwrap_or_else(|| "matmul/dps48".into());
    let seconds = get("--seconds", 60) as u64;
    let threads = get("--threads", 12) as usize;
    let cap = get("--cap", 64);
    let outdir = args
        .iter()
        .position(|a| a == "--out")
        .and_then(|i| args.get(i + 1).cloned())
        .unwrap_or_else(|| "matmul/found48q".into());
    std::fs::create_dir_all(&outdir).unwrap();

    rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build_global()
        .unwrap();

    let seed = load_seed(&dir);
    assert_eq!(seed.len(), 48);
    assert!(verify(&seed), "seed must verify");
    println!("seed loaded + exactly verified (48 summands)");
    if args.iter().any(|a| a == "--emit-lean") {
        // dump the gauged seed as a Lean literal (List (V16 x V16 x V16))
        let v = |x: &Vec16| -> String {
            format!("⟨#[{}], {}⟩",
                    x.nums.map(|n| n.to_string()).join(", "), x.exp)
        };
        let mut txt = String::from("def seed : List Summand := [\n");
        for (idx, t) in seed.iter().enumerate() {
            txt += &format!("  ⟨{}, {}, {}⟩{}\n", v(&t.a), v(&t.b), v(&t.c),
                            if idx + 1 < seed.len() { "," } else { "" });
        }
        txt += "]\n";
        println!("{txt}");
        return;
    }
    if args.iter().any(|a| a == "--pursue") {
        pursue(&seed, cap, &outdir);
        return;
    }
    if let Some(pi) = args.iter().position(|a| a == "--graph") {
        let path = args.get(pi + 1).cloned()
            .unwrap_or_else(|| "graph48.json".into());
        graph_export(&seed, cap, &path);
        return;
    }
    if let Some(pi) = args.iter().position(|a| a == "--nmrand") {
        let maxk: usize = args.get(pi + 1).and_then(|v| v.parse().ok())
            .unwrap_or(8);
        let n = get("--n", 2000) as usize;
        nmrand(&seed, cap, maxk, n);
        return;
    }
    if args.iter().any(|a| a == "--worked") {
        worked(&seed, cap);
        return;
    }
    if args.iter().any(|a| a == "--pursue6") {
        let beam = get("--beam", 1500) as usize;
        let ks = get("--samples", 60) as usize;
        let dp = get("--depth", 6) as u32;
        let budget = get("--budget", 500_000_000) as u64;
        let resume6 = args.iter().position(|a| a == "--resume6")
            .and_then(|i| args.get(i + 1).cloned());
        let startlv = get("--startlevel", 0) as u32;
        pursue6(&seed, cap, beam, ks, dp, budget, &outdir,
                resume6.as_deref(), startlv);
        return;
    }
    if let Some(pi) = args.iter().position(|a| a == "--pursue5") {
        let k: usize = args.get(pi + 1).and_then(|v| v.parse().ok())
            .unwrap_or(200);
        let budget = get("--budget", 200_000_000) as u64;
        let fringe = args.iter().any(|a| a == "--fringe-only");
        let resume = args.iter().any(|a| a == "--resume");
        pursue5(&seed, cap, k, budget, fringe, resume, &outdir);
        return;
    }
    if let Some(pi) = args.iter().position(|a| a == "--pursue4") {
        let sp: u32 = args
            .get(pi + 1)
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);
        pursue4(&seed, cap, sp, &outdir);
        return;
    }
    if let Some(pi) = args.iter().position(|a| a == "--pursue3") {
        let depth: u32 = args
            .get(pi + 1)
            .and_then(|v| v.parse().ok())
            .unwrap_or(2);
        pursue3(&seed, cap, depth, &outdir);
        return;
    }

    let best_rank = AtomicU32::new(48);
    let n_split = AtomicU64::new(0);
    let n_coinc = AtomicU64::new(0);   // targeted flips applied
    let n_reduce = AtomicU64::new(0);  // merges performed
    let distinct48 = Mutex::new(std::collections::HashSet::<u64>::new());
    let walks = AtomicU64::new(0);
    let moves = AtomicU64::new(0);
    let t0 = Instant::now();

    (0..threads as u64).into_par_iter().for_each(|tid| {
        let mut rng = Rng(0x9e3779b97f4a7c15 ^ (tid.wrapping_mul(0xa54ff53a5f1d36f1) + 1));
        while t0.elapsed().as_secs() < seconds {
            let mut s = seed.clone();
            walks.fetch_add(1, Ordering::Relaxed);
            // one walk: split -> flip storm -> greedy reductions
            for _step in 0..2000 {
                if t0.elapsed().as_secs() >= seconds {
                    break;
                }
                let r = rng.next() % 100;
                if r < 8 || s.len() == 48 {
                    // split (also forced when at base rank: isolated seed)
                    if s.len() <= 52 {
                        let i = rng.below(s.len());
                        let k = rng.below(s.len());
                        let slot = rng.below(3);
                        let mu = LAMS[rng.below(6)];
                        if try_split(&mut s, i, k, slot, mu, cap) {
                            moves.fetch_add(1, Ordering::Relaxed);
                            n_split.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                    // at the ceiling: skip the split, keep flipping
                } else if r < 92 {
                    // flip: sample among ACTUALLY shared-factor pairs
                    use std::collections::HashMap;
                    let mut eligible: Vec<(usize, usize, usize)> = Vec::new();
                    for slot in 0..3 {
                        let mut m: HashMap<&Vec16, usize> = HashMap::new();
                        for (idx, t) in s.iter().enumerate() {
                            if let Some(&prev) = m.get(fac(t, slot)) {
                                eligible.push((prev, idx, slot));
                            } else {
                                m.insert(fac(t, slot), idx);
                            }
                        }
                    }
                    if eligible.is_empty() {
                        continue;
                    }
                    let (i, j, slot) = eligible[rng.below(eligible.len())];
                    let (i, j) = if rng.next() & 1 == 0 { (i, j) } else { (j, i) };
                    // prefer a coincidence-solving lambda when one
                    // exists (this is what makes Q-flips productive);
                    // fall back to a random small lambda
                    let cands = coincidence_lams(&s, i, j, slot);
                    let targeted = !cands.is_empty() && rng.next() % 4 != 0;
                    let lam = if targeted {
                        cands[rng.below(cands.len())].1
                    } else {
                        LAMS[rng.below(6)]
                    };
                    if try_flip(&mut s, i, j, slot, lam, cap) {
                        moves.fetch_add(1, Ordering::Relaxed);
                        if targeted {
                            n_coinc.fetch_add(1, Ordering::Relaxed);
                        }
                    }
                } else {
                    // reduction sweep
                    while try_reduce(&mut s, cap * 4) {
                        moves.fetch_add(1, Ordering::Relaxed);
                        n_reduce.fetch_add(1, Ordering::Relaxed);
                    }
                    let rank = s.len() as u32;
                    if rank < best_rank.load(Ordering::Relaxed) {
                        if verify(&s) {
                            best_rank.store(rank, Ordering::Relaxed);
                            let path = format!("{outdir}/rank{rank}_{tid}.txt");
                            let mut txt = String::new();
                            for t in &s {
                                txt += &format!("{:?} | {:?} | {:?}\n",
                                                (t.a.nums, t.a.exp),
                                                (t.b.nums, t.b.exp),
                                                (t.c.nums, t.c.exp));
                            }
                            std::fs::write(&path, txt).ok();
                            println!(
                                "[{:.0}s] *** RANK {} VERIFIED *** -> {}",
                                t0.elapsed().as_secs_f32(), rank, path
                            );
                        } else {
                            println!("[{:.0}s] rank {} FAILED verify (bug!)",
                                     t0.elapsed().as_secs_f32(), rank);
                        }
                    }
                    if rank == 48 {
                        let h = scheme_hash(&s);
                        let mut d = distinct48.lock().unwrap();
                        if d.insert(h) && d.len() % 500 == 0 {
                            println!("[{:.0}s] distinct rank-48 forms: {}",
                                     t0.elapsed().as_secs_f32(), d.len());
                        }
                    }
                }
            }
            // paranoia: verify a sample of end states
            if rng.next() % 64 == 0 && !verify(&s) {
                println!("WALK END VERIFY FAILED (bug!)");
            }
        }
    });

    println!(
        "funnel: {} splits, {} targeted flips, {} reductions",
        n_split.load(Ordering::Relaxed),
        n_coinc.load(Ordering::Relaxed),
        n_reduce.load(Ordering::Relaxed)
    );
    println!(
        "\n{} walks, {} moves in {:.0}s; best rank {}; distinct rank-48 \
         canonical forms collected: {}",
        walks.load(Ordering::Relaxed),
        moves.load(Ordering::Relaxed),
        t0.elapsed().as_secs_f32(),
        best_rank.load(Ordering::Relaxed),
        distinct48.lock().unwrap().len()
    );
}
