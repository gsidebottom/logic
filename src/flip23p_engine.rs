// Rational-flip machinery over a PRIME FIELD — the zkML port.
// flip23 (3x3x23, Z[1/2]) re-based onto F_p, default p = Goldilocks
// (2^64 - 2^32 + 1, the Plonky2/STARK field).  Motivation: in SNARK
// arithmetization multiplication constraints cost and additions are
// free, so bilinear RANK is the proof-cost driver; rank is
// field-dependent (cf. 4x4:47 mod 2 with no known char-0 equal), and
// nobody has run flip search over big proof fields.  A verified
// rank-22 over Goldilocks would be a shippable zkML cost reduction.
//
// Over F_p the engine gets STRONGER than its Q parent:
//   - no coefficient growth, no magnitude cap;
//   - every coincidence solution is usable (no dyadic filter): all
//     coplanar triples become productive flips — H4's "raw material"
//     is fully spendable;
//   - gauge = monic normalization (leading coeff 1; scalars fold
//     into the c-slot), so proportional <=> equal, as before.
//
// DIMENSION-GENERIC: the enclosing include! module provides, besides
// P and fmul, the consts DIM (matrix dimension), RANK0 (seed rank),
// DEF_DIR and DEF_OUT.  flip23p instantiates 3x3x23; flip48p 4x4x48.
//
// Modes: storm (default), --census, --native, --lams, --pursue7
// (mix-and-quench descent), --pursue8 (constructor), --repair K
// (delete K seed terms, beam-rebuild the residual in <= K-1: any
// success is an instant rank drop; exhaustive over C(RANK0,K)).
// Pool format: one line per summand "[NN u64s] | [..] | [..]",
// blocks separated by "---" (no exp fields).
//
// Usage: flipNNp [--prime g|b|m31] [--dir D] [--seconds N]
//                [--threads N] [--out D] [--maxw W] [--maxd D]
//                [--census | --native | --lams | --pursue7 --hi H
//                 --mix M | --pursue8 --beam B --cands C --maxr R |
//                 --repair K]

use rayon::prelude::*;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

// field primitives (P, fmul) and shape consts (DIM, RANK0, DEF_DIR,
// DEF_OUT) are provided by the enclosing field module
const NN: usize = DIM * DIM; // vectorized matrix length
const NAIVE: usize = DIM * NN; // naive rank = DIM^3

#[inline]
fn fadd(a: u64, b: u64) -> u64 {
    let (s, c) = a.overflowing_add(b);
    let mut r = s;
    if c || r >= P {
        r = r.wrapping_sub(P);
    }
    r
}
#[inline]
fn fsub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a.wrapping_sub(b).wrapping_add(P) }
}
#[inline]
fn fneg(a: u64) -> u64 {
    if a == 0 { 0 } else { P - a }
}
fn fpow(mut b: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            r = fmul(r, b);
        }
        b = fmul(b, b);
        e >>= 1;
    }
    r
}
fn finv(a: u64) -> u64 {
    debug_assert!(a != 0);
    fpow(a, P - 2)
}

// ---------- vectors over F_p ----------
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
struct FVec {
    nums: [u64; NN],
}

impl FVec {
    fn is_zero(&self) -> bool {
        self.nums.iter().all(|&x| x == 0)
    }
    /// monic canonical form: self = scalar * canon, canon's leading
    /// nonzero coefficient = 1.  Returns (canon, scalar).
    fn canon(&self) -> (FVec, u64) {
        let mut lead = 0u64;
        for &x in self.nums.iter() {
            if x != 0 {
                lead = x;
                break;
            }
        }
        if lead == 0 {
            return (self.clone(), 1);
        }
        let li = finv(lead);
        let mut v = [0u64; NN];
        for (o, &x) in v.iter_mut().zip(self.nums.iter()) {
            *o = fmul(x, li);
        }
        (FVec { nums: v }, lead)
    }
    /// self + lam * other
    fn add_scaled(&self, other: &FVec, lam: u64) -> FVec {
        let mut v = [0u64; NN];
        for i in 0..NN {
            v[i] = fadd(self.nums[i], fmul(lam, other.nums[i]));
        }
        FVec { nums: v }
    }
    fn scaled(&self, lam: u64) -> FVec {
        let mut v = [0u64; NN];
        for i in 0..NN {
            v[i] = fmul(self.nums[i], lam);
        }
        FVec { nums: v }
    }
}

#[derive(Clone)]
struct Summand {
    a: FVec, // monic
    b: FVec, // monic
    c: FVec, // carries the scalar
}

impl Summand {
    fn gauge(a: FVec, b: FVec, c: FVec) -> Option<Summand> {
        if a.is_zero() || b.is_zero() || c.is_zero() {
            return None;
        }
        let (ca, sa) = a.canon();
        let (cb, sb) = b.canon();
        let c2 = c.scaled(fmul(sa, sb));
        if c2.is_zero() {
            return None;
        }
        Some(Summand { a: ca, b: cb, c: c2 })
    }
}

fn fac<'s>(t: &'s Summand, slot: usize) -> &'s FVec {
    match slot {
        0 => &t.a,
        1 => &t.b,
        _ => &t.c,
    }
}

// ---------- exact verification over F_p ----------
fn verify(scheme: &[Summand]) -> bool {
    for x in 0..NN {
        for y in 0..NN {
            for z in 0..NN {
                let mut s = 0u64;
                for t in scheme {
                    s = fadd(s, fmul(fmul(t.a.nums[x], t.b.nums[y]), t.c.nums[z]));
                }
                let want =
                    if x % DIM == y / DIM && x / DIM == z / DIM && y % DIM == z % DIM { 1 } else { 0 };
                if s != want {
                    return false;
                }
            }
        }
    }
    true
}

// ---------- moves ----------
/// flip on shared slot-`slot` factor of i, j (post-gauge EQUAL there):
/// transfer slot t1 of i gains lam*f_j; t2 of j loses lam*f_i.
fn try_flip(scheme: &mut Vec<Summand>, i: usize, j: usize, slot: usize, lam: u64) -> bool {
    if i == j || lam == 0 || fac(&scheme[i], slot) != fac(&scheme[j], slot) {
        return false;
    }
    let others: [usize; 2] = match slot {
        0 => [1, 2],
        1 => [0, 2],
        _ => [0, 1],
    };
    let (t1, t2) = (others[0], others[1]);
    let bi = fac(&scheme[i], t1).add_scaled(fac(&scheme[j], t1), lam);
    let cj = fac(&scheme[j], t2).add_scaled(fac(&scheme[i], t2), fneg(lam));
    if bi.is_zero() || cj.is_zero() {
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
    match (
        Summand::gauge(ni.a, ni.b, ni.c),
        Summand::gauge(nj.a, nj.b, nj.c),
    ) {
        (Some(gi), Some(gj)) => {
            scheme[i] = gi;
            scheme[j] = gj;
            true
        }
        _ => false,
    }
}

/// split summand i against k in slot `slot` with mu != 0:
/// f_i = mu*f_k + (f_i - mu*f_k); rank +1, first part SHARES the slot.
fn try_split(scheme: &mut Vec<Summand>, i: usize, k: usize, slot: usize, mu: u64) -> bool {
    if i == k || mu == 0 {
        return false;
    }
    let fi = fac(&scheme[i], slot);
    let fk = fac(&scheme[k], slot);
    let rest = fi.add_scaled(fk, fneg(mu));
    if rest.is_zero() {
        return false; // proportional: that's a reduction, not a split
    }
    let part = fk.scaled(mu);
    let mk = |f: FVec, t: &Summand| -> Option<Summand> {
        match slot {
            0 => Summand::gauge(f, t.b.clone(), t.c.clone()),
            1 => Summand::gauge(t.a.clone(), f, t.c.clone()),
            _ => Summand::gauge(t.a.clone(), t.b.clone(), f),
        }
    };
    match (mk(part, &scheme[i]), mk(rest, &scheme[i])) {
        (Some(s1), Some(s2)) => {
            scheme[i] = s1;
            scheme.push(s2);
            true
        }
        _ => false,
    }
}

/// proportionality over F_p: v = rho * w for some rho != 0
fn prop_ratio(v: &FVec, w: &FVec) -> Option<u64> {
    let mut rho = 0u64;
    for i in 0..NN {
        match (v.nums[i], w.nums[i]) {
            (0, 0) => {}
            (0, _) | (_, 0) => return None,
            (a, b) => {
                let r = fmul(a, finv(b));
                if rho == 0 {
                    rho = r;
                } else if rho != r {
                    return None;
                }
            }
        }
    }
    if rho == 0 { None } else { Some(rho) }
}

/// reduction: i, j sharing two slots (a,b monic: equality; c:
/// proportionality) merge into one summand on the third slot.
fn try_reduce(scheme: &mut Vec<Summand>) -> bool {
    let n = scheme.len();
    for i in 0..n {
        for j in i + 1..n {
            let sa = scheme[i].a == scheme[j].a;
            let sb = scheme[i].b == scheme[j].b;
            if sa && sb {
                let c = scheme[i].c.add_scaled(&scheme[j].c, 1);
                let (a, b) = (scheme[i].a.clone(), scheme[i].b.clone());
                scheme.swap_remove(j);
                if c.is_zero() {
                    scheme.swap_remove(i);
                } else if let Some(g) = Summand::gauge(a, b, c) {
                    scheme[i] = g;
                } else {
                    return false;
                }
                return true;
            }
            // a shared + c proportional -> merge b
            if sa {
                if let Some(rho) = prop_ratio(&scheme[j].c, &scheme[i].c) {
                    let b = scheme[i].b.add_scaled(&scheme[j].b, rho);
                    let (a, c) = (scheme[i].a.clone(), scheme[i].c.clone());
                    scheme.swap_remove(j);
                    if b.is_zero() {
                        scheme.swap_remove(i);
                    } else if let Some(g) = Summand::gauge(a, b, c) {
                        scheme[i] = g;
                    } else {
                        return false;
                    }
                    return true;
                }
            }
            if sb {
                if let Some(rho) = prop_ratio(&scheme[j].c, &scheme[i].c) {
                    let a = scheme[i].a.add_scaled(&scheme[j].a, rho);
                    let (b, c) = (scheme[i].b.clone(), scheme[i].c.clone());
                    scheme.swap_remove(j);
                    if a.is_zero() {
                        scheme.swap_remove(i);
                    } else if let Some(g) = Summand::gauge(a, b, c) {
                        scheme[i] = g;
                    } else {
                        return false;
                    }
                    return true;
                }
            }
        }
    }
    false
}

/// solved flips: for pair (i,j) sharing `slot`, find (t, lam, m) with
/// f_i + lam f_j = mu f_m in transfer slot t.  Over F_p EVERY
/// nondegenerate Cramer solution is usable.
fn coincidence_lams(scheme: &[Summand], i: usize, j: usize, slot: usize) -> Vec<(usize, u64, usize)> {
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
            // lam*fj - mu*fm = -fi at two pivot coords, then full check
            let mut piv = None;
            'fp: for p in 0..NN {
                for q in p + 1..NN {
                    let det = fsub(
                        fmul(fj.nums[p], fneg(fm.nums[q])),
                        fmul(fj.nums[q], fneg(fm.nums[p])),
                    );
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
            let nl = fsub(
                fmul(fneg(fi.nums[p]), fneg(fm.nums[q])),
                fmul(fneg(fi.nums[q]), fneg(fm.nums[p])),
            );
            let nmu = fsub(
                fmul(fj.nums[p], fneg(fi.nums[q])),
                fmul(fj.nums[q], fneg(fi.nums[p])),
            );
            if nl == 0 || nmu == 0 {
                continue;
            }
            let di = finv(det);
            let lam = fmul(nl, di);
            let ok = (0..NN).all(|x| {
                fadd(
                    fadd(fmul(det, fi.nums[x]), fmul(nl, fj.nums[x])),
                    fneg(fmul(nmu, fm.nums[x])),
                ) == 0
            });
            if ok {
                out.push((t1, lam, m));
            }
        }
    }
    out
}

// ---------- hashing / metrics ----------
fn scheme_hash(scheme: &[Summand]) -> u64 {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let mut keys: Vec<[u64; 3 * NN]> = scheme
        .iter()
        .map(|t| {
            let mut k = [0u64; 3 * NN];
            k[..NN].copy_from_slice(&t.a.nums);
            k[NN..2 * NN].copy_from_slice(&t.b.nums);
            k[2 * NN..].copy_from_slice(&t.c.nums);
            k
        })
        .collect();
    keys.sort_unstable();
    let mut h = DefaultHasher::new();
    keys.hash(&mut h);
    h.finish()
}

fn weight(s: &[Summand]) -> usize {
    s.iter()
        .map(|t| {
            t.a.nums.iter().filter(|x| **x != 0).count()
                + t.b.nums.iter().filter(|x| **x != 0).count()
                + t.c.nums.iter().filter(|x| **x != 0).count()
        })
        .sum()
}

fn dsum(s: &[Summand]) -> usize {
    use std::collections::HashSet;
    let da: HashSet<&FVec> = s.iter().map(|t| &t.a).collect();
    let db: HashSet<&FVec> = s.iter().map(|t| &t.b).collect();
    da.len() + db.len()
}

fn over_caps(old: &[Summand], new: &[Summand], maxw: usize, maxd: usize) -> bool {
    if maxw > 0 {
        let nw = weight(new);
        if nw > maxw && nw > weight(old) {
            return true;
        }
    }
    if maxd > 0 {
        let nd = dsum(new);
        if nd > maxd && nd > dsum(old) {
            return true;
        }
    }
    false
}

fn state_metrics(st: &[Summand]) -> (usize, usize, usize) {
    // (shared pairs, coincidences, nearmiss) over F_p
    let n = st.len();
    let (mut shared, mut coinc, mut nearmiss) = (0usize, 0usize, 0usize);
    for ss in 0..3usize {
        for x in 0..n {
            for y in x + 1..n {
                if fac(&st[x], ss) == fac(&st[y], ss) {
                    shared += 1;
                    let c1 = coincidence_lams(st, x, y, ss);
                    let c2 = coincidence_lams(st, y, x, ss);
                    coinc += c1.len() + c2.len();
                    let mut ms: Vec<usize> =
                        c1.iter().chain(c2.iter()).map(|&(_, _, m)| m).collect();
                    ms.sort_unstable();
                    ms.dedup();
                    nearmiss += ms.len();
                }
            }
        }
    }
    (shared, coinc, nearmiss)
}



// ---------- pursue8: constructor (residual rank-one subtraction) ----------
// The builder arm: start from the full matmul tensor as a residual and
// SUBTRACT rank-one terms u (x) v (x) w until zero — AlphaTensor's move
// space, beam-guided here.  Not confined to any flip component: every
// scheme expressible over F_p is in this search space by construction.

fn target_tensor() -> Vec<u64> {
    let mut r = vec![0u64; NN * NN * NN];
    for x in 0..NN {
        for y in 0..NN {
            for z in 0..NN {
                if x % DIM == y / DIM && x / DIM == z / DIM && y % DIM == z % DIM {
                    r[(x * NN + y) * NN + z] = 1;
                }
            }
        }
    }
    r
}

fn matn_rank(m: &[[u64; NN]; NN]) -> usize {
    let mut a = *m;
    let mut rank = 0;
    for col in 0..NN {
        let mut piv = None;
        for row in rank..NN {
            if a[row][col] != 0 {
                piv = Some(row);
                break;
            }
        }
        let Some(pr) = piv else { continue };
        a.swap(rank, pr);
        let inv = finv(a[rank][col]);
        for c in col..NN {
            a[rank][c] = fmul(a[rank][c], inv);
        }
        for row in 0..NN {
            if row != rank && a[row][col] != 0 {
                let f = a[row][col];
                for c in col..NN {
                    a[row][c] = fsub(a[row][c], fmul(f, a[rank][c]));
                }
            }
        }
        rank += 1;
        if rank == NN {
            break;
        }
    }
    rank
}

/// score = sum of z-slice ranks (heuristic remaining-rank measure)
fn residual_score(r: &[u64]) -> usize {
    let mut total = 0;
    for z in 0..NN {
        let mut m = [[0u64; NN]; NN];
        for x in 0..NN {
            for y in 0..NN {
                m[x][y] = r[(x * NN + y) * NN + z];
            }
        }
        total += matn_rank(&m);
    }
    total
}

fn residual_nz_fibers(r: &[u64]) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for x in 0..NN {
        for y in 0..NN {
            if (0..NN).any(|z| r[(x * NN + y) * NN + z] != 0) {
                out.push((x, y));
            }
        }
    }
    out
}

fn subtract_term(r: &mut [u64], u: &[u64; NN], v: &[u64; NN], w: &[u64; NN]) {
    for x in 0..NN {
        if u[x] == 0 {
            continue;
        }
        for y in 0..NN {
            if v[y] == 0 {
                continue;
            }
            let uv = fmul(u[x], v[y]);
            for z in 0..NN {
                if w[z] != 0 {
                    let idx = (x * NN + y) * NN + z;
                    r[idx] = fsub(r[idx], fmul(uv, w[z]));
                }
            }
        }
    }
}

// ---------- pursue7: mix-and-quench descent ----------
/// solve f_base + lam*f_other = mu*f_target over F_p (lam, mu != 0)
fn solve_toward(fb: &FVec, fo: &FVec, ft: &FVec) -> Option<u64> {
    let mut piv = None;
    'fp: for p in 0..NN {
        for q in p + 1..NN {
            let det = fsub(
                fmul(fo.nums[p], fneg(ft.nums[q])),
                fmul(fo.nums[q], fneg(ft.nums[p])),
            );
            if det != 0 {
                piv = Some((p, q, det));
                break 'fp;
            }
        }
    }
    let (p, q, det) = piv?;
    let nl = fsub(
        fmul(fneg(fb.nums[p]), fneg(ft.nums[q])),
        fmul(fneg(fb.nums[q]), fneg(ft.nums[p])),
    );
    let nmu = fsub(
        fmul(fo.nums[p], fneg(fb.nums[q])),
        fmul(fo.nums[q], fneg(fb.nums[p])),
    );
    if nl == 0 || nmu == 0 {
        return None;
    }
    let ok = (0..NN).all(|x| {
        fadd(
            fadd(fmul(det, fb.nums[x]), fmul(nl, fo.nums[x])),
            fneg(fmul(nmu, ft.nums[x])),
        ) == 0
    });
    if !ok {
        return None;
    }
    Some(fmul(nl, finv(det)))
}

/// one-slot alignment: a/b post-gauge equality; c proportionality
fn aligned(st: &[Summand], i: usize, j: usize, s: usize) -> bool {
    if s < 2 {
        fac(&st[i], s) == fac(&st[j], s)
    } else {
        prop_ratio(&st[i].c, &st[j].c).is_some()
    }
}

/// closing move: find an aligned pair (i,j) and ONE flip that rewrites
/// j's second-slot factor to become proportional to i's — after which
/// try_reduce fires on (i,j).  Applies the first solution found.
fn try_closing(st: &mut Vec<Summand>) -> bool {
    let n = st.len();
    for i in 0..n {
        for j in 0..n {
            if i == j {
                continue;
            }
            for s_al in 0..3usize {
                if !aligned(st, i.min(j), i.max(j), s_al) {
                    continue;
                }
                for t in (0..3usize).filter(|&t| t != s_al) {
                    for s2 in (0..3usize).filter(|&s2| s2 != t) {
                        let others: [usize; 2] = match s2 {
                            0 => [1, 2],
                            1 => [0, 2],
                            _ => [0, 1],
                        };
                        for k in 0..n {
                            if k == j || k == i || fac(&st[j], s2) != fac(&st[k], s2) {
                                continue;
                            }
                            if let Some(lam) = solve_toward(
                                fac(&st[j], t), fac(&st[k], t), fac(&st[i], t),
                            ) {
                                let mut c = st.clone();
                                let ok = if t == others[0] {
                                    try_flip(&mut c, j, k, s2, lam)
                                } else {
                                    try_flip(&mut c, k, j, s2, fneg(lam))
                                };
                                if ok {
                                    *st = c;
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    false
}

// ---------- seed loading (SMS, integers reduced mod p) ----------
fn load_seed(dir: &str) -> Vec<Summand> {
    let tof = |v: i64| -> u64 {
        if v >= 0 { v as u64 % P } else { P - ((-v) as u64 % P) }
    };
    // entries may be integers "n" or fractions "n/d" (fine over F_p)
    let fval = move |s: &str| -> u64 {
        match s.split_once('/') {
            None => tof(s.parse::<i64>().expect("seed entry")),
            Some((a, b)) => {
                let na = tof(a.parse::<i64>().expect("seed numerator"));
                let nb = tof(b.parse::<i64>().expect("seed denominator"));
                assert!(nb != 0, "seed denominator divisible by p");
                fmul(na, finv(nb))
            }
        }
    };
    let parse = move |p: &str| -> Vec<Vec<(usize, u64)>> {
        let txt = std::fs::read_to_string(p).expect(p);
        let mut dims = None;
        let mut rows: Vec<Vec<(usize, u64)>> = Vec::new();
        for ln in txt.lines() {
            let ln = ln.trim();
            if ln.is_empty() || ln.starts_with('#') {
                continue;
            }
            let f: Vec<&str> = ln.split_whitespace().collect();
            if dims.is_none() {
                dims = Some(f[0].parse::<usize>().unwrap());
                rows = vec![Vec::new(); dims.unwrap()];
                continue;
            }
            let (i, j): (usize, usize) = (f[0].parse().unwrap(), f[1].parse().unwrap());
            if i == 0 && j == 0 {
                break;
            }
            rows[i - 1].push((j - 1, fval(f[2])));
        }
        rows
    };
    let mk = |sparse: &Vec<(usize, u64)>| -> FVec {
        let mut nums = [0u64; NN];
        for &(j, n) in sparse {
            nums[j] = n;
        }
        FVec { nums }
    };
    let l = parse(&format!("{dir}/L.sms"));
    let r = parse(&format!("{dir}/R.sms"));
    let p = parse(&format!("{dir}/P.sms")); // NN x RANK0 -> transpose
    let mut pt: Vec<Vec<(usize, u64)>> = vec![Vec::new(); l.len()];
    for (z, row) in p.iter().enumerate() {
        for &(i, n) in row {
            pt[i].push((z, n));
        }
    }
    (0..l.len())
        .map(|i| Summand::gauge(mk(&l[i]), mk(&r[i]), mk(&pt[i])).expect("seed"))
        .collect()
}

fn dump(s: &[Summand], path: &str) {
    let mut txt = String::new();
    for t in s {
        txt += &format!("{:?} | {:?} | {:?}\n", t.a.nums, t.b.nums, t.c.nums);
    }
    std::fs::write(path, txt).ok();
}

const SLOT: [&str; 3] = ["a", "b", "c"];

pub fn run(args: Vec<String>) {
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
        .unwrap_or_else(|| DEF_DIR.into());
    let seconds = get("--seconds", 60) as u64;
    let threads = get("--threads", 12) as usize;
    let maxw = get("--maxw", 0) as usize;
    let maxd = get("--maxd", 0) as usize;
    let cap = get("--cap", (RANK0 + 4) as i64) as usize;
    let outdir = args
        .iter()
        .position(|a| a == "--out")
        .and_then(|i| args.get(i + 1).cloned())
        .unwrap_or_else(|| DEF_OUT.into());
    std::fs::create_dir_all(&outdir).unwrap();
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build_global();

    let seed = load_seed(&dir);
    if seed.len() != RANK0 {
        println!("note: seed rank {} != module default {RANK0} \
                  (fine for pursue9/census)", seed.len());
    }
    assert!(verify(&seed), "seed must verify over F_p");
    println!("seed loaded + exactly verified over F_p, p = {P} ({RANK0} summands)");

    if args.iter().any(|a| a == "--census") {
        let (sh, co, nm) = state_metrics(&seed);
        println!("seed metrics over F_p: shared {sh}  coinc {co}  nearmiss {nm}  \
                  weight {}  dsum {}", weight(&seed), dsum(&seed));
        for ss in 0..3usize {
            for x in 0..seed.len() {
                for y in x + 1..seed.len() {
                    if fac(&seed[x], ss) == fac(&seed[y], ss) {
                        println!("  shared {}-factor pair ({x},{y})", SLOT[ss]);
                    }
                }
            }
        }
        return;
    }

    // shared closure machinery for --native / --lams
    let closure_mode = if args.iter().any(|a| a == "--native") {
        Some(true) // solved flips only
    } else if args.iter().any(|a| a == "--lams") {
        Some(false) // random-lam flips too (sampled)
    } else {
        None
    };
    if let Some(solved_only) = closure_mode {
        use std::collections::{HashSet, VecDeque};
        let maxn = get("--max", 200_000) as usize;
        let t0 = Instant::now();
        let mut seen: HashSet<u64> = HashSet::new();
        let mut q = VecDeque::new();
        seen.insert(scheme_hash(&seed));
        q.push_back(seed.clone());
        let mut rng = 0x9e3779b97f4a7c15u64;
        let mut nextr = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        let (mut n_states, mut n_red) = (0usize, 0usize);
        while let Some(st) = q.pop_front() {
            n_states += 1;
            let mut r = st.clone();
            let mut red = false;
            while try_reduce(&mut r) {
                red = true;
            }
            if red && r.len() < RANK0 && verify(&r) {
                n_red += 1;
                println!("!!! RANK {} OVER F_p — verified !!!", r.len());
                dump(&r, &format!("{outdir}/RECORDP_rank{}_{}.txt", r.len(), n_red));
            }
            let n = st.len();
            for ss in 0..3usize {
                for x in 0..n {
                    for y in x + 1..n {
                        if fac(&st[x], ss) != fac(&st[y], ss) {
                            continue;
                        }
                        if seen.len() >= maxn {
                            continue;
                        }
                        for &(oi, oj) in &[(x, y), (y, x)] {
                            for &(t, lam, _m) in &coincidence_lams(&st, oi, oj, ss) {
                                let others: [usize; 2] = match ss {
                                    0 => [1, 2],
                                    1 => [0, 2],
                                    _ => [0, 1],
                                };
                                let mut c = st.clone();
                                let ok = if t == others[0] {
                                    try_flip(&mut c, oi, oj, ss, lam)
                                } else {
                                    try_flip(&mut c, oj, oi, ss, fneg(lam))
                                };
                                if ok && seen.insert(scheme_hash(&c)) {
                                    q.push_back(c);
                                }
                            }
                            if !solved_only {
                                for _ in 0..4 {
                                    let lam = nextr() % P;
                                    let mut c = st.clone();
                                    if lam != 0
                                        && try_flip(&mut c, oi, oj, ss, lam)
                                        && seen.insert(scheme_hash(&c))
                                    {
                                        q.push_back(c);
                                    }
                                }
                            }
                        }
                    }
                }
            }
            if n_states % 25_000 == 0 {
                println!(
                    "[closure] visited {n_states}  frontier {}  seen {}  red {n_red}  {:.0}s",
                    q.len(), seen.len(), t0.elapsed().as_secs_f64()
                );
            }
        }
        println!(
            "closure ({}): visited {n_states} (seen {}{})  reductions<23: {n_red}  {:.1}s",
            if solved_only { "solved flips" } else { "solved + random lams" },
            seen.len(),
            if seen.len() >= maxn { ", TRUNCATED" } else { ", complete" },
            t0.elapsed().as_secs_f64()
        );
        return;
    }

    let repair_k = get("--repair", 0) as usize;
    if repair_k >= 2 {
        // repair mode: delete K seed terms, beam-rebuild the residual
        // (= the sum of the K deleted rank-one tensors) in <= K-1 new
        // terms.  ANY completion is an instant verified rank drop.
        // Exhaustive over C(RANK0, K) subsets (lex-unranked, strided
        // across threads), time-capped by --seconds.
        let k = repair_k;
        let budget = k - 1;
        let beamw = get("--beam", 4) as usize;
        let cands = get("--cands", 24) as usize;
        let secsp = get("--seconds", 600) as u64;
        let n = seed.len();
        fn binom(n: usize, k: usize) -> u64 {
            if k > n {
                return 0;
            }
            let k = k.min(n - k);
            let mut r: u128 = 1;
            for i in 0..k {
                r = r * (n - i) as u128 / (i + 1) as u128;
            }
            r as u64
        }
        let unrank = |mut idx: u64, n: usize, k: usize| -> Vec<usize> {
            let mut out = Vec::with_capacity(k);
            let (mut need, mut start) = (k, 0usize);
            while need > 0 {
                let c = binom(n - start - 1, need - 1);
                if idx < c {
                    out.push(start);
                    need -= 1;
                } else {
                    idx -= c;
                }
                start += 1;
            }
            out
        };
        let total = binom(n, k);
        println!(
            "repair: delete {k} of {n}, beam-rebuild in <= {budget} \
             ({total} subsets, beam {beamw}, cands {cands})"
        );
        use std::collections::BTreeMap;
        let hist: Mutex<BTreeMap<usize, u64>> = Mutex::new(BTreeMap::new());
        let n_done = AtomicU64::new(0);
        let n_none = AtomicU64::new(0);
        let n_rec = AtomicU64::new(0);
        let t0 = Instant::now();
        (0..threads as u64).into_par_iter().for_each(|tid| {
            let mut rng = 0x2545_f491_4f6c_dd1du64
                ^ (tid.wrapping_mul(0x9e37_79b9_7f4a_7c15) + 1);
            let mut next = move || {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                rng
            };
            let mut idx = tid;
            while idx < total && t0.elapsed().as_secs() < secsp {
                let del = unrank(idx, n, k);
                idx += threads as u64;
                // residual = sum of the deleted terms' tensors
                let mut r0 = vec![0u64; NN * NN * NN];
                for &i in &del {
                    let mut negc = [0u64; NN];
                    for (o, &x) in negc.iter_mut().zip(seed[i].c.nums.iter()) {
                        *o = fneg(x);
                    }
                    subtract_term(&mut r0, &seed[i].a.nums, &seed[i].b.nums, &negc);
                }
                let mut beam: Vec<(Vec<u64>, Vec<([u64; NN], [u64; NN], [u64; NN])>)> =
                    vec![(r0, Vec::new())];
                let mut best: Option<Vec<([u64; NN], [u64; NN], [u64; NN])>> = None;
                for _step in 0..=budget {
                    let mut pool: Vec<(usize, usize, Vec<u64>,
                                       Vec<([u64; NN], [u64; NN], [u64; NN])>)> = Vec::new();
                    for (r, terms) in &beam {
                        let fibers = residual_nz_fibers(r);
                        if terms.len() + fibers.len() <= budget {
                            let mut ts = terms.clone();
                            let mut rr = r.clone();
                            for &(x, y) in &fibers {
                                let mut u = [0u64; NN];
                                let mut v = [0u64; NN];
                                let mut w = [0u64; NN];
                                u[x] = 1;
                                v[y] = 1;
                                for z in 0..NN {
                                    w[z] = rr[(x * NN + y) * NN + z];
                                }
                                subtract_term(&mut rr, &u, &v, &w);
                                ts.push((u, v, w));
                            }
                            debug_assert!(rr.iter().all(|&e| e == 0));
                            if best.as_ref().map_or(true, |b| ts.len() < b.len()) {
                                best = Some(ts);
                            }
                        }
                        if terms.len() >= budget {
                            continue;
                        }
                        for ci in 0..cands {
                            let mut u = [0u64; NN];
                            let mut v = [0u64; NN];
                            if ci & 1 == 0 && fibers.len() >= 2 {
                                let (x1, y1) =
                                    fibers[(next() % fibers.len() as u64) as usize];
                                let (x2, y2) =
                                    fibers[(next() % fibers.len() as u64) as usize];
                                u[x1] = 1;
                                if x2 != x1 {
                                    u[x2] = if next() & 1 == 0 { 1 } else { P - 1 };
                                }
                                v[y1] = 1;
                                if y2 != y1 {
                                    v[y2] = if next() & 1 == 0 { 1 } else { P - 1 };
                                }
                            } else {
                                let su = 1 + (next() % DIM as u64) as usize;
                                let sv = 1 + (next() % DIM as u64) as usize;
                                for _ in 0..su {
                                    let e = if next() & 1 == 0 { 1 } else { P - 1 };
                                    u[(next() % NN as u64) as usize] = e;
                                }
                                for _ in 0..sv {
                                    let e = if next() & 1 == 0 { 1 } else { P - 1 };
                                    v[(next() % NN as u64) as usize] = e;
                                }
                            }
                            let mut f = [0u64; NN];
                            for x in 0..NN {
                                if u[x] == 0 {
                                    continue;
                                }
                                for y in 0..NN {
                                    if v[y] == 0 {
                                        continue;
                                    }
                                    let uv = fmul(u[x], v[y]);
                                    for z in 0..NN {
                                        f[z] = fadd(
                                            f[z],
                                            fmul(uv, r[(x * NN + y) * NN + z]),
                                        );
                                    }
                                }
                            }
                            if f.iter().all(|&e| e == 0) {
                                continue;
                            }
                            let su2 =
                                u.iter().fold(0u64, |a, &e| fadd(a, fmul(e, e)));
                            let sv2 =
                                v.iter().fold(0u64, |a, &e| fadd(a, fmul(e, e)));
                            let s = fmul(su2, sv2);
                            if s == 0 {
                                continue;
                            }
                            let si = finv(s);
                            let mut w = [0u64; NN];
                            for z in 0..NN {
                                w[z] = fmul(f[z], si);
                            }
                            let mut rr = r.clone();
                            subtract_term(&mut rr, &u, &v, &w);
                            let fib2 = residual_nz_fibers(&rr).len();
                            let proj = terms.len() + 1 + fib2;
                            let nz = rr.iter().filter(|&&e| e != 0).count();
                            let mut ts = terms.clone();
                            ts.push((u, v, w));
                            pool.push((proj * 1000 + nz, nz, rr, ts));
                        }
                    }
                    if pool.is_empty() {
                        break;
                    }
                    pool.sort_by(|a, b| (a.0, a.1).cmp(&(b.0, b.1)));
                    pool.truncate(beamw);
                    beam = pool.into_iter().map(|(_, _, r, t)| (r, t)).collect();
                }
                let done = n_done.fetch_add(1, Ordering::Relaxed) + 1;
                match best {
                    None => {
                        n_none.fetch_add(1, Ordering::Relaxed);
                    }
                    Some(ts) => {
                        let tot = n - k + ts.len();
                        *hist.lock().unwrap().entry(tot).or_insert(0) += 1;
                        if tot < n {
                            let mut sch: Vec<Summand> = seed
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| !del.contains(i))
                                .map(|(_, s)| s.clone())
                                .collect();
                            let mut ok = true;
                            for (u, v, w) in &ts {
                                match Summand::gauge(
                                    FVec { nums: *u },
                                    FVec { nums: *v },
                                    FVec { nums: *w },
                                ) {
                                    Some(g) => sch.push(g),
                                    None => {
                                        ok = false;
                                        break;
                                    }
                                }
                            }
                            if ok && verify(&sch) {
                                n_rec.fetch_add(1, Ordering::Relaxed);
                                let path = format!(
                                    "{outdir}/RECORDP_repair_rank{tot}_{tid}.txt"
                                );
                                dump(&sch, &path);
                                println!(
                                    "[{:.0}s] *** REPAIR RANK {tot} OVER F_p VERIFIED \
                                     (deleted {del:?}) *** -> {path}",
                                    t0.elapsed().as_secs_f32()
                                );
                            } else if ok {
                                println!(
                                    "repair assembled-scheme verify FAILED (rank {tot}) — bug!"
                                );
                            }
                        }
                    }
                }
                if done % 100_000 == 0 {
                    println!(
                        "[{:.0}s] repair: {done}/{total} subsets",
                        t0.elapsed().as_secs_f32()
                    );
                }
            }
        });
        println!(
            "repair k={k}: {}/{} subsets in {:.0}s; no-completion {}; records {}",
            n_done.load(Ordering::Relaxed),
            total,
            t0.elapsed().as_secs_f64(),
            n_none.load(Ordering::Relaxed),
            n_rec.load(Ordering::Relaxed)
        );
        println!(
            "rebuilt-total histogram (kept + rebuilt): {:?}",
            hist.lock().unwrap()
        );
        return;
    }

    if args.iter().any(|a| a == "--pursue8") {
        // constructor: beam search over rank-one subtractions from the
        // residual tensor; exact fiber-peel finishing rule guarantees a
        // valid terminal count per restart.  Terminal-count histogram is
        // the instrument; <= 22 over the field is the record event.
        let beamw = get("--beam", 8) as usize;
        let cands = get("--cands", 160) as usize;
        let maxr = get("--maxr", NAIVE as i64) as usize;
        let secsp = get("--seconds", 600) as u64;
        let rankscore = args.iter().any(|a| a == "--rankscore");
        use std::collections::BTreeMap;
        let hist: Mutex<BTreeMap<usize, u64>> = Mutex::new(BTreeMap::new());
        let built23: Mutex<std::collections::HashSet<u64>> =
            Mutex::new(Default::default());
        let n_restarts = AtomicU64::new(0);
        let best_seen = AtomicU32::new(u32::MAX);
        let t0 = Instant::now();
        (0..threads as u64).into_par_iter().for_each(|tid| {
            let mut rng = 0x517c_c1b7_2722_0a95u64
                ^ (tid.wrapping_mul(0x2545_f491_4f6c_dd1d) + 1);
            let mut next = move || {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                rng
            };
            while t0.elapsed().as_secs() < secsp {
                n_restarts.fetch_add(1, Ordering::Relaxed);
                // beam of (residual, terms)
                let mut beam: Vec<(Vec<u64>, Vec<([u64; NN], [u64; NN], [u64; NN])>)> =
                    vec![(target_tensor(), Vec::new())];
                let mut finished: Option<Vec<([u64; NN], [u64; NN], [u64; NN])>> = None;
                'steps: for _step in 0..maxr {
                    let mut pool: Vec<(usize, usize, Vec<u64>,
                                       Vec<([u64; NN], [u64; NN], [u64; NN])>)> = Vec::new();
                    for (r, terms) in &beam {
                        // finishing rule: peel remaining fibers exactly
                        let fibers = residual_nz_fibers(r);
                        if terms.len() + fibers.len() <= maxr {
                            let mut ts = terms.clone();
                            let mut rr = r.clone();
                            for &(x, y) in &fibers {
                                let mut u = [0u64; NN];
                                let mut v = [0u64; NN];
                                let mut w = [0u64; NN];
                                u[x] = 1;
                                v[y] = 1;
                                for z in 0..NN {
                                    w[z] = rr[(x * NN + y) * NN + z];
                                }
                                subtract_term(&mut rr, &u, &v, &w);
                                ts.push((u, v, w));
                            }
                            debug_assert!(rr.iter().all(|&e| e == 0));
                            if finished.as_ref().map_or(true, |f| ts.len() < f.len()) {
                                finished = Some(ts);
                            }
                            // fall through: keep improving on this state
                        }
                        // candidate expansions
                        for ci in 0..cands {
                            let mut u = [0u64; NN];
                            let mut v = [0u64; NN];
                            if ci & 1 == 0 && fibers.len() >= 2 {
                                // fiber-targeted: aim at two ACTIVE fibers
                                let (x1, y1) = fibers[(next() % fibers.len() as u64) as usize];
                                let (x2, y2) = fibers[(next() % fibers.len() as u64) as usize];
                                u[x1] = 1;
                                if x2 != x1 {
                                    u[x2] = if next() & 1 == 0 { 1 } else { P - 1 };
                                }
                                v[y1] = 1;
                                if y2 != y1 {
                                    v[y2] = if next() & 1 == 0 { 1 } else { P - 1 };
                                }
                            } else {
                                let su = 1 + (next() % DIM as u64) as usize;
                                let sv = 1 + (next() % DIM as u64) as usize;
                                for _ in 0..su {
                                    let e = if next() & 1 == 0 { 1 } else { P - 1 };
                                    u[(next() % NN as u64) as usize] = e;
                                }
                                for _ in 0..sv {
                                    let e = if next() & 1 == 0 { 1 } else { P - 1 };
                                    v[(next() % NN as u64) as usize] = e;
                                }
                            }
                            // contraction f_z and normalizer s
                            let mut f = [0u64; NN];
                            for x in 0..NN {
                                if u[x] == 0 { continue; }
                                for y in 0..NN {
                                    if v[y] == 0 { continue; }
                                    let uv = fmul(u[x], v[y]);
                                    for z in 0..NN {
                                        f[z] = fadd(f[z],
                                            fmul(uv, r[(x * NN + y) * NN + z]));
                                    }
                                }
                            }
                            if f.iter().all(|&e| e == 0) {
                                continue;
                            }
                            let su2 = u.iter().fold(0u64, |a, &e| fadd(a, fmul(e, e)));
                            let sv2 = v.iter().fold(0u64, |a, &e| fadd(a, fmul(e, e)));
                            let s = fmul(su2, sv2);
                            if s == 0 {
                                continue;
                            }
                            let si = finv(s);
                            let mut w = [0u64; NN];
                            for z in 0..NN {
                                w[z] = fmul(f[z], si);
                            }
                            let mut rr = r.clone();
                            subtract_term(&mut rr, &u, &v, &w);
                            // primary score: projected completion total
                            // (terms so far + 1 + remaining fibers);
                            // secondary: slice-rank sum
                            let fib2 = residual_nz_fibers(&rr).len();
                            let proj = terms.len() + 1 + fib2;
                            // --rankscore: slice-rank-sum primary (can
                            // reward Strassen-hump moves that temporarily
                            // raise fiber count); default: projected-total
                            let sc = if rankscore {
                                residual_score(&rr) * 1000 + proj
                            } else {
                                proj * 1000 + residual_score(&rr)
                            };
                            let nz = rr.iter().filter(|&&e| e != 0).count();
                            let mut ts = terms.clone();
                            ts.push((u, v, w));
                            pool.push((sc, nz, rr, ts));
                        }
                    }
                    if pool.is_empty() {
                        break 'steps;
                    }
                    pool.sort_by(|a, b| (a.0, a.1).cmp(&(b.0, b.1)));
                    pool.truncate(beamw);
                    beam = pool.into_iter().map(|(_, _, r, t)| (r, t)).collect();
                }
                let total = match &finished {
                    Some(ts) => ts.len(),
                    None => continue, // no valid completion this restart
                };
                *hist.lock().unwrap().entry(total).or_insert(0) += 1;
                if (total as u32) < best_seen.load(Ordering::Relaxed) {
                    best_seen.store(total as u32, Ordering::Relaxed);
                    println!("[{:.0}s] pursue8 best so far: {total} terms",
                             t0.elapsed().as_secs_f32());
                }
                if total <= RANK0 {
                    // reconstruct + exact-verify the built scheme
                    let ts = finished.unwrap();
                    let sch: Option<Vec<Summand>> = ts.iter()
                        .map(|(u, v, w)| Summand::gauge(
                            FVec { nums: *u }, FVec { nums: *v }, FVec { nums: *w }))
                        .collect();
                    if let Some(sch) = sch {
                        if verify(&sch) {
                            if total < RANK0 {
                                let path = format!(
                                    "{outdir}/RECORDP_built_rank{total}_{tid}.txt");
                                dump(&sch, &path);
                                println!(
                                    "[{:.0}s] *** BUILT RANK {} OVER F_p — VERIFIED *** -> {}",
                                    t0.elapsed().as_secs_f32(), total, path);
                            } else {
                                let h = scheme_hash(&sch);
                                let mut d = built23.lock().unwrap();
                                if d.insert(h) {
                                    let nn = d.len();
                                    if nn <= 2000 || nn % 1000 == 0 {
                                        use std::io::Write;
                                        if let Ok(mut fpool) = std::fs::OpenOptions::new()
                                            .create(true).append(true)
                                            .open(format!("{outdir}/pool8.txt"))
                                        {
                                            for t in &sch {
                                                writeln!(fpool, "{:?} | {:?} | {:?}",
                                                    t.a.nums, t.b.nums, t.c.nums).ok();
                                            }
                                            writeln!(fpool, "---").ok();
                                        }
                                    }
                                }
                            }
                        } else {
                            println!("pursue8 built-scheme verify FAILED ({total} terms) — bug!");
                        }
                    }
                }
            }
        });
        println!(
            "pursue8: {} restarts in {:.0}s; best {} terms; distinct built-23s {}",
            n_restarts.load(Ordering::Relaxed),
            t0.elapsed().as_secs_f64(),
            best_seen.load(Ordering::Relaxed),
            built23.lock().unwrap().len()
        );
        println!("terminal-count histogram: {:?}", hist.lock().unwrap());
        return;
    }

    if args.iter().any(|a| a == "--pursue9") {
        // persistent Kauers-Moosbauer walk: test reductions at EVERY
        // step and continue from reduced states (contrast pursue7,
        // which quenches only at walk end). Each thread runs one
        // trajectory for the whole budget: reduce greedily whenever
        // possible, otherwise a random eligible flip; split (rank+1)
        // only when stuck, capped at --hi.
        let hi = get("--hi", (RANK0 + 2) as i64) as usize;
        let secsp = get("--seconds", 600) as u64;
        use std::collections::BTreeMap;
        let best_hist: Mutex<BTreeMap<usize, u64>> = Mutex::new(BTreeMap::new());
        let n_red = AtomicU64::new(0);
        let n_flip = AtomicU64::new(0);
        let n_split = AtomicU64::new(0);
        let global_best = AtomicU32::new(seed.len() as u32);
        let t0 = Instant::now();
        (0..threads as u64).into_par_iter().for_each(|tid| {
            let mut rng = 0x243f_6a88_85a3_08d3u64
                ^ (tid.wrapping_mul(0x9e37_79b9_7f4a_7c15) + 1);
            let mut next = move || {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                rng
            };
            let mut s = seed.clone();
            let mut traj_best = s.len();
            let mut stuck = 0u32;
            let mut last_report = 0u64;
            // reductions are only legal after a flip: a fresh split's
            // two parts share both non-split slots and try_reduce
            // would instantly undo the split (split/merge livelock)
            let mut can_reduce = true;
            while t0.elapsed().as_secs() < secsp {
                // 1. take every reduction available, immediately
                if can_reduce && try_reduce(&mut s) {
                    n_red.fetch_add(1, Ordering::Relaxed);
                    stuck = 0;
                    let r = s.len();
                    if r < traj_best {
                        traj_best = r;
                        let gb = global_best.load(Ordering::Relaxed);
                        if (r as u32) < gb && verify(&s) {
                            global_best.store(r as u32, Ordering::Relaxed);
                            let path = format!(
                                "{outdir}/RECORDP_p9_rank{r}_{tid}.txt");
                            dump(&s, &path);
                            println!(
                                "[{:.0}s] *** pursue9 rank {} VERIFIED *** -> {}",
                                t0.elapsed().as_secs_f32(), r, path);
                        }
                    }
                    continue;
                }
                // 2. random eligible flip (lam = 1 is the only unit at p=2;
                //    at odd p sample a random nonzero lam)
                use std::collections::HashMap;
                let mut eligible: Vec<(usize, usize, usize)> = Vec::new();
                for slot in 0..3 {
                    let mut m: HashMap<&FVec, usize> = HashMap::new();
                    for (idx, t) in s.iter().enumerate() {
                        if let Some(&prev) = m.get(fac(t, slot)) {
                            eligible.push((prev, idx, slot));
                        } else {
                            m.insert(fac(t, slot), idx);
                        }
                    }
                }
                let mut moved = false;
                if !eligible.is_empty() {
                    let (i, j, slot) =
                        eligible[(next() % eligible.len() as u64) as usize];
                    let (i, j) = if next() & 1 == 0 { (i, j) } else { (j, i) };
                    // small-lambda skeleton: over big F_p a uniformly
                    // random lam makes exact factor coincidences (what
                    // reductions need) recur with prob ~1/p — never.
                    // Walk mostly on images of +-1, +-2, +-1/2, with
                    // occasional generic excursions. At p=2 unchanged.
                    let lam = if P > 2 && next() % 8 != 0 {
                        match next() % 6 {
                            0 => 1,
                            1 => P - 1,
                            2 => 2 % P,
                            3 => P - 2 % P,
                            4 => (P + 1) / 2,     // 1/2 mod odd p
                            _ => (P - 1) / 2,     // -1/2 mod odd p
                        }
                    } else {
                        loop {
                            let x = next() % P;
                            if x != 0 {
                                break x;
                            }
                        }
                    };
                    if try_flip(&mut s, i, j, slot, lam) {
                        n_flip.fetch_add(1, Ordering::Relaxed);
                        moved = true;
                        can_reduce = true;
                    }
                }
                if !moved {
                    stuck += 1;
                }
                // 3. split when stuck or with small probability, capped
                if (stuck > 8 || next() % 512 == 0) && s.len() < hi {
                    let i = (next() % s.len() as u64) as usize;
                    let k = (next() % s.len() as u64) as usize;
                    let slot = (next() % 3) as usize;
                    let mu = loop {
                        let x = next() % P;
                        if x != 0 {
                            break x;
                        }
                    };
                    if try_split(&mut s, i, k, slot, mu) {
                        n_split.fetch_add(1, Ordering::Relaxed);
                        stuck = 0;
                        can_reduce = false;
                    }
                }
                // periodic thread-0 status
                if tid == 0 {
                    let el = t0.elapsed().as_secs();
                    if el >= last_report + 120 {
                        last_report = el;
                        println!(
                            "[{el}s] pursue9: best rank {}  reductions {}                               flips {}  splits {}",
                            global_best.load(Ordering::Relaxed),
                            n_red.load(Ordering::Relaxed),
                            n_flip.load(Ordering::Relaxed),
                            n_split.load(Ordering::Relaxed));
                    }
                }
            }
            *best_hist.lock().unwrap().entry(traj_best).or_insert(0) += 1;
        });
        println!(
            "pursue9: best rank {} in {:.0}s; reductions {}  flips {}  splits {}",
            global_best.load(Ordering::Relaxed),
            t0.elapsed().as_secs_f64(),
            n_red.load(Ordering::Relaxed),
            n_flip.load(Ordering::Relaxed),
            n_split.load(Ordering::Relaxed));
        println!("per-trajectory best-rank histogram: {:?}",
                 best_hist.lock().unwrap());
        return;
    }

    if args.iter().any(|a| a == "--pursue7") {
        // mix-and-quench descent: diffuse at a high rank band, then
        // greedily reduce + close; instrument terminal ranks (the
        // corrected obstruction diagnostic: where do chains stall?)
        let mix = get("--mix", 1500) as u64;
        let hi = get("--hi", (RANK0 + 3) as i64) as usize;
        let secsp = get("--seconds", 600) as u64;
        use std::collections::BTreeMap;
        let hist: Mutex<BTreeMap<usize, u64>> = Mutex::new(BTreeMap::new());
        let land23: Mutex<std::collections::HashSet<u64>> =
            Mutex::new(Default::default());
        let n_close = AtomicU64::new(0);
        let n_red = AtomicU64::new(0);
        let n_walks = AtomicU64::new(0);
        let t0 = Instant::now();
        (0..threads as u64).into_par_iter().for_each(|tid| {
            let mut rng = 0x9e3779b97f4a7c15u64
                ^ (tid.wrapping_mul(0xa54ff53a5f1d36f1) + 1);
            let mut next = move || {
                rng ^= rng << 13;
                rng ^= rng >> 7;
                rng ^= rng << 17;
                rng
            };
            while t0.elapsed().as_secs() < secsp {
                let mut s = seed.clone();
                n_walks.fetch_add(1, Ordering::Relaxed);
                // MIX: splits up to the band + random-lam flips; no descent
                for _ in 0..mix {
                    let r = next() % 100;
                    if s.len() < hi && (r < 25 || s.len() == RANK0) {
                        let i = (next() % s.len() as u64) as usize;
                        let k = (next() % s.len() as u64) as usize;
                        let slot = (next() % 3) as usize;
                        let mu = loop {
                            let x = next() % P;
                            if x != 0 {
                                break x;
                            }
                        };
                        try_split(&mut s, i, k, slot, mu);
                    } else {
                        use std::collections::HashMap;
                        let mut eligible: Vec<(usize, usize, usize)> = Vec::new();
                        for slot in 0..3 {
                            let mut m: HashMap<&FVec, usize> = HashMap::new();
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
                        let (i, j, slot) =
                            eligible[(next() % eligible.len() as u64) as usize];
                        let (i, j) = if next() & 1 == 0 { (i, j) } else { (j, i) };
                        let lam = loop {
                            let x = next() % P;
                            if x != 0 {
                                break x;
                            }
                        };
                        try_flip(&mut s, i, j, slot, lam);
                    }
                }
                // QUENCH: reductions first, closing moves second
                loop {
                    if try_reduce(&mut s) {
                        n_red.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                    if try_closing(&mut s) {
                        n_close.fetch_add(1, Ordering::Relaxed);
                        continue;
                    }
                    break;
                }
                let r = s.len();
                *hist.lock().unwrap().entry(r).or_insert(0) += 1;
                if r < RANK0 {
                    if verify(&s) {
                        let path = format!("{outdir}/RECORDP_rank{r}_{tid}.txt");
                        dump(&s, &path);
                        println!(
                            "[{:.0}s] *** RANK {} OVER F_p VERIFIED (pursue7) *** -> {}",
                            t0.elapsed().as_secs_f32(), r, path
                        );
                    } else {
                        println!("pursue7 terminal verify FAILED at rank {r} (bug!)");
                    }
                } else if r == RANK0 && verify(&s) {
                    let h = scheme_hash(&s);
                    let mut d = land23.lock().unwrap();
                    if d.insert(h) {
                        let nn = d.len();
                        if nn <= 2000 || nn % 1000 == 0 {
                            use std::io::Write;
                            if let Ok(mut f) = std::fs::OpenOptions::new()
                                .create(true)
                                .append(true)
                                .open(format!("{outdir}/pool7.txt"))
                            {
                                for t in &s {
                                    writeln!(f, "{:?} | {:?} | {:?}",
                                             t.a.nums, t.b.nums, t.c.nums).ok();
                                }
                                writeln!(f, "---").ok();
                            }
                        }
                    }
                }
            }
        });
        println!(
            "pursue7: {} walks in {:.0}s; closings {}  reductions {}  distinct {RANK0}-landings {}",
            n_walks.load(Ordering::Relaxed),
            t0.elapsed().as_secs_f64(),
            n_close.load(Ordering::Relaxed),
            n_red.load(Ordering::Relaxed),
            land23.lock().unwrap().len()
        );
        println!("terminal-rank histogram: {:?}", hist.lock().unwrap());
        return;
    }

    // ---------- storm ----------
    if maxw > 0 || maxd > 0 {
        println!(
            "thin storm (ratchet): maxw {maxw} maxd {maxd}; seed weight {} dsum {}",
            weight(&seed), dsum(&seed)
        );
    }
    let best_rank = AtomicU32::new(RANK0 as u32);
    let n_split = AtomicU64::new(0);
    let n_coinc = AtomicU64::new(0);
    let n_reduce = AtomicU64::new(0);
    let n_wrej = AtomicU64::new(0);
    let distinct23 = Mutex::new(std::collections::HashSet::<u64>::new());
    let walks = AtomicU64::new(0);
    let moves = AtomicU64::new(0);
    let t0 = Instant::now();

    (0..threads as u64).into_par_iter().for_each(|tid| {
        let mut rng = 0x9e3779b97f4a7c15u64 ^ (tid.wrapping_mul(0xa54ff53a5f1d36f1) + 1);
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };

        while t0.elapsed().as_secs() < seconds {
            let mut s = seed.clone();
            walks.fetch_add(1, Ordering::Relaxed);
            for _step in 0..2000 {
                if t0.elapsed().as_secs() >= seconds {
                    break;
                }
                let r = next() % 100;
                if r < 8 || s.len() == 23 {
                    if s.len() <= cap {
                        let i = (next() % s.len() as u64) as usize;
                        let k = (next() % s.len() as u64) as usize;
                        let slot = (next() % 3) as usize;
                        let mu = loop { let x = next() % P; if x != 0 { break x; } };
                        let saved = if maxw > 0 || maxd > 0 { Some(s.clone()) } else { None };
                        if try_split(&mut s, i, k, slot, mu) {
                            if let Some(sv) = saved.filter(|sv| over_caps(sv, &s, maxw, maxd)) {
                                s = sv;
                                n_wrej.fetch_add(1, Ordering::Relaxed);
                            } else {
                                moves.fetch_add(1, Ordering::Relaxed);
                                n_split.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                } else if r < 92 {
                    use std::collections::HashMap;
                    let mut eligible: Vec<(usize, usize, usize)> = Vec::new();
                    for slot in 0..3 {
                        let mut m: HashMap<&FVec, usize> = HashMap::new();
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
                    let (i, j, slot) = eligible[(next() % eligible.len() as u64) as usize];
                    let (i, j) = if next() & 1 == 0 { (i, j) } else { (j, i) };
                    let cands = coincidence_lams(&s, i, j, slot);
                    let targeted = !cands.is_empty() && next() % 4 != 0;
                    let lam = if targeted {
                        cands[(next() % cands.len() as u64) as usize].1
                    } else {
                        loop { let x = next() % P; if x != 0 { break x; } }
                    };
                    let saved = if maxw > 0 || maxd > 0 { Some(s.clone()) } else { None };
                    if try_flip(&mut s, i, j, slot, lam) {
                        if let Some(sv) = saved.filter(|sv| over_caps(sv, &s, maxw, maxd)) {
                            s = sv;
                            n_wrej.fetch_add(1, Ordering::Relaxed);
                        } else {
                            moves.fetch_add(1, Ordering::Relaxed);
                            if targeted {
                                n_coinc.fetch_add(1, Ordering::Relaxed);
                            }
                        }
                    }
                } else {
                    while try_reduce(&mut s) {
                        moves.fetch_add(1, Ordering::Relaxed);
                        n_reduce.fetch_add(1, Ordering::Relaxed);
                    }
                    let rank = s.len() as u32;
                    if rank < best_rank.load(Ordering::Relaxed) {
                        if verify(&s) {
                            best_rank.store(rank, Ordering::Relaxed);
                            let path = format!("{outdir}/RECORDP_rank{rank}_{tid}.txt");
                            dump(&s, &path);
                            println!(
                                "[{:.0}s] *** RANK {} OVER F_p VERIFIED *** -> {}",
                                t0.elapsed().as_secs_f32(), rank, path
                            );
                        } else {
                            println!("WALK VERIFY FAILED at rank {} (bug!)", s.len());
                        }
                    }
                    if rank == RANK0 as u32 {
                        let h = scheme_hash(&s);
                        let mut d = distinct23.lock().unwrap();
                        if d.insert(h) {
                            let n = d.len();
                            if n <= 2000 || n % 1000 == 0 {
                                use std::io::Write;
                                if let Ok(mut f) = std::fs::OpenOptions::new()
                                    .create(true)
                                    .append(true)
                                    .open(format!("{outdir}/poolp.txt"))
                                {
                                    for t in &s {
                                        writeln!(f, "{:?} | {:?} | {:?}",
                                                 t.a.nums, t.b.nums, t.c.nums).ok();
                                    }
                                    writeln!(f, "---").ok();
                                }
                            }
                            if n % 500 == 0 {
                                println!("[{:.0}s] distinct rank-{RANK0} forms (F_p): {}",
                                         t0.elapsed().as_secs_f32(), n);
                            }
                        }
                    }
                }
            }
            if next() % 64 == 0 && !verify(&s) {
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
        "\n{} walks, {} moves in {:.0}s; best rank {}; distinct rank-23 \
         canonical forms collected: {}",
        walks.load(Ordering::Relaxed),
        moves.load(Ordering::Relaxed),
        t0.elapsed().as_secs_f32(),
        best_rank.load(Ordering::Relaxed),
        distinct23.lock().unwrap().len()
    );
    if maxw > 0 || maxd > 0 {
        println!("thin storm: maxw {maxw} maxd {maxd}; moves rejected over caps: {}",
                 n_wrej.load(Ordering::Relaxed));
    }
}
