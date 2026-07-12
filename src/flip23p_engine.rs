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
// v1 modes: storm (default), --census, --native, --lams.  Campaign
// modes (pursue5/6, graph, worked, nmrand) port in v2.
// Pool format: one line per summand "[9 u64s] | [..] | [..]", blocks
// separated by "---" (no exp fields — this is a different ecosystem
// from the Q pools).
//
// Usage: flip23p [--dir matmul/mm23] [--seconds N] [--threads N]
//                [--out found23p] [--maxw W] [--maxd D]
//         flip23p --census | --native [--max N] | --lams [--max N]

use rayon::prelude::*;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

// field primitives (P, fmul) are provided by the enclosing field module

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
struct Vec9 {
    nums: [u64; 9],
}

impl Vec9 {
    fn is_zero(&self) -> bool {
        self.nums.iter().all(|&x| x == 0)
    }
    /// monic canonical form: self = scalar * canon, canon's leading
    /// nonzero coefficient = 1.  Returns (canon, scalar).
    fn canon(&self) -> (Vec9, u64) {
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
        let mut v = [0u64; 9];
        for (o, &x) in v.iter_mut().zip(self.nums.iter()) {
            *o = fmul(x, li);
        }
        (Vec9 { nums: v }, lead)
    }
    /// self + lam * other
    fn add_scaled(&self, other: &Vec9, lam: u64) -> Vec9 {
        let mut v = [0u64; 9];
        for i in 0..9 {
            v[i] = fadd(self.nums[i], fmul(lam, other.nums[i]));
        }
        Vec9 { nums: v }
    }
    fn scaled(&self, lam: u64) -> Vec9 {
        let mut v = [0u64; 9];
        for i in 0..9 {
            v[i] = fmul(self.nums[i], lam);
        }
        Vec9 { nums: v }
    }
}

#[derive(Clone)]
struct Summand {
    a: Vec9, // monic
    b: Vec9, // monic
    c: Vec9, // carries the scalar
}

impl Summand {
    fn gauge(a: Vec9, b: Vec9, c: Vec9) -> Option<Summand> {
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

fn fac<'s>(t: &'s Summand, slot: usize) -> &'s Vec9 {
    match slot {
        0 => &t.a,
        1 => &t.b,
        _ => &t.c,
    }
}

// ---------- exact verification over F_p ----------
fn verify(scheme: &[Summand]) -> bool {
    for x in 0..9usize {
        for y in 0..9usize {
            for z in 0..9usize {
                let mut s = 0u64;
                for t in scheme {
                    s = fadd(s, fmul(fmul(t.a.nums[x], t.b.nums[y]), t.c.nums[z]));
                }
                let want =
                    if x % 3 == y / 3 && x / 3 == z / 3 && y % 3 == z % 3 { 1 } else { 0 };
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
    let mk = |f: Vec9, t: &Summand| -> Option<Summand> {
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
fn prop_ratio(v: &Vec9, w: &Vec9) -> Option<u64> {
    let mut rho = 0u64;
    for i in 0..9 {
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
            'fp: for p in 0..9 {
                for q in p + 1..9 {
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
            let ok = (0..9).all(|x| {
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
    let mut keys: Vec<[u64; 27]> = scheme
        .iter()
        .map(|t| {
            let mut k = [0u64; 27];
            k[..9].copy_from_slice(&t.a.nums);
            k[9..18].copy_from_slice(&t.b.nums);
            k[18..].copy_from_slice(&t.c.nums);
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
    let da: HashSet<&Vec9> = s.iter().map(|t| &t.a).collect();
    let db: HashSet<&Vec9> = s.iter().map(|t| &t.b).collect();
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

fn rank3(v: &Vec9) -> usize {
    // exact 3x3 rank over F_p via minors
    let m = &v.nums;
    let det = fadd(
        fsub(
            fmul(m[0], fsub(fmul(m[4], m[8]), fmul(m[5], m[7]))),
            fmul(m[1], fsub(fmul(m[3], m[8]), fmul(m[5], m[6]))),
        ),
        fmul(m[2], fsub(fmul(m[3], m[7]), fmul(m[4], m[6]))),
    );
    if det != 0 {
        return 3;
    }
    for r1 in 0..3 {
        for r2 in r1 + 1..3 {
            for c1 in 0..3 {
                for c2 in c1 + 1..3 {
                    if fsub(
                        fmul(m[3 * r1 + c1], m[3 * r2 + c2]),
                        fmul(m[3 * r1 + c2], m[3 * r2 + c1]),
                    ) != 0
                    {
                        return 2;
                    }
                }
            }
        }
    }
    if v.is_zero() { 0 } else { 1 }
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


// ---------- pursue7: mix-and-quench descent ----------
/// solve f_base + lam*f_other = mu*f_target over F_p (lam, mu != 0)
fn solve_toward(fb: &Vec9, fo: &Vec9, ft: &Vec9) -> Option<u64> {
    let mut piv = None;
    'fp: for p in 0..9 {
        for q in p + 1..9 {
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
    let ok = (0..9).all(|x| {
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
    let parse = |p: &str| -> Vec<Vec<(usize, i64)>> {
        let txt = std::fs::read_to_string(p).expect(p);
        let mut dims = None;
        let mut rows: Vec<Vec<(usize, i64)>> = Vec::new();
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
            let v: i64 = f[2].parse().expect("integer seed entries only in v1");
            rows[i - 1].push((j - 1, v));
        }
        rows
    };
    let tof = |v: i64| -> u64 {
        if v >= 0 { v as u64 % P } else { P - ((-v) as u64 % P) }
    };
    let mk = |sparse: &Vec<(usize, i64)>| -> Vec9 {
        let mut nums = [0u64; 9];
        for &(j, n) in sparse {
            nums[j] = tof(n);
        }
        Vec9 { nums }
    };
    let l = parse(&format!("{dir}/L.sms"));
    let r = parse(&format!("{dir}/R.sms"));
    let p = parse(&format!("{dir}/P.sms")); // 9 x 23 -> transpose
    let mut pt: Vec<Vec<(usize, i64)>> = vec![Vec::new(); 23];
    for (z, row) in p.iter().enumerate() {
        for &(i, n) in row {
            pt[i].push((z, n));
        }
    }
    (0..23)
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
        .unwrap_or_else(|| "matmul/mm23".into());
    let seconds = get("--seconds", 60) as u64;
    let threads = get("--threads", 12) as usize;
    let maxw = get("--maxw", 0) as usize;
    let maxd = get("--maxd", 0) as usize;
    let outdir = args
        .iter()
        .position(|a| a == "--out")
        .and_then(|i| args.get(i + 1).cloned())
        .unwrap_or_else(|| "matmul/found23p".into());
    std::fs::create_dir_all(&outdir).unwrap();
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build_global();

    let seed = load_seed(&dir);
    assert_eq!(seed.len(), 23);
    assert!(verify(&seed), "seed must verify over F_p");
    println!("seed loaded + exactly verified over F_p, p = {P} (23 summands)");

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
            if red && r.len() < 23 && verify(&r) {
                n_red += 1;
                println!("!!! RANK {} OVER GOLDILOCKS — verified !!!", r.len());
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

    if args.iter().any(|a| a == "--pursue7") {
        // mix-and-quench descent: diffuse at a high rank band, then
        // greedily reduce + close; instrument terminal ranks (the
        // corrected obstruction diagnostic: where do chains stall?)
        let mix = get("--mix", 1500) as u64;
        let hi = get("--hi", 26) as usize;
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
                    if s.len() < hi && (r < 25 || s.len() == 23) {
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
                            let mut m: HashMap<&Vec9, usize> = HashMap::new();
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
                if r < 23 {
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
                } else if r == 23 && verify(&s) {
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
            "pursue7: {} walks in {:.0}s; closings {}  reductions {}  distinct 23-landings {}",
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
    let best_rank = AtomicU32::new(23);
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
                    if s.len() <= 27 {
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
                        let mut m: HashMap<&Vec9, usize> = HashMap::new();
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
                                "[{:.0}s] *** RANK {} OVER GOLDILOCKS VERIFIED *** -> {}",
                                t0.elapsed().as_secs_f32(), rank, path
                            );
                        } else {
                            println!("WALK VERIFY FAILED at rank {} (bug!)", s.len());
                        }
                    }
                    if rank == 23 {
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
                                println!("[{:.0}s] distinct rank-23 forms (F_p): {}",
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
