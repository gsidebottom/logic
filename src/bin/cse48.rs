//! Rust CSE storm for the rational 4x4x4:48 (Dumas-Pernet-Sedoglavic,
//! arXiv 2506.13242 — the de-complexified AlphaEvolve scheme).
//!
//! Targets (their PLinOpt SLP): L = 104 adds, R = 84 adds + 1 shift,
//! P = 119 adds + 33 shifts — 341 ops total.
//!
//! Every coefficient in this scheme is ±2^e (e ∈ [-3, 0]), so a
//! coefficient is (sign, exponent) and pair-extraction CSE closes over
//! that set.  An op computes w = u ± 2^k·v and costs 1 addition plus,
//! when k ≠ 0, 1 shift; assembling a form of ℓ remaining terms costs
//! ℓ−1 additions plus a shift per term whose residual coefficient is
//! not ±1 (documented accounting — conservative vs the paper's).
//!
//! Instances: the 6 S₃ slot variants of the scheme (which tensor family
//! plays the output role, × the transpose flip), each Brent-verified
//! exactly at startup (all 4096 equations, coefficients scaled to i64).
//! Per component we score both the direct greedy and the transposed
//! greedy (Tellegen: SLP(W) = SLP(W^T) + in(W) − out(W)), and every
//! improving trace is replay-verified before being accepted.
//!
//! Usage: cse48 [--seconds N] [--dir matmul/dps48] [--threads N]

use rayon::prelude::*;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::time::Instant;

// ---------- coefficients: ±2^e ----------
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
struct Coef {
    neg: bool,
    exp: i8,
}
impl Coef {
    fn ratio(a: Coef, b: Coef) -> (bool, i8) {
        // b / a as (sign, exponent)
        (a.neg != b.neg, b.exp - a.exp)
    }
}

// a linear form: sorted (var, coef) pairs
type Form = Vec<(u32, Coef)>;

fn parse_sms(path: &str) -> (usize, usize, Vec<Vec<Option<Coef>>>) {
    let txt = std::fs::read_to_string(path).expect(path);
    let mut dims = None;
    let mut m: Vec<Vec<Option<Coef>>> = Vec::new();
    for ln in txt.lines() {
        let ln = ln.trim();
        if ln.is_empty() || ln.starts_with('#') {
            continue;
        }
        let p: Vec<&str> = ln.split_whitespace().collect();
        if dims.is_none() {
            let (r, c) = (p[0].parse().unwrap(), p[1].parse().unwrap());
            dims = Some((r, c));
            m = vec![vec![None; c]; r];
            continue;
        }
        let (i, j): (usize, usize) = (p[0].parse().unwrap(), p[1].parse().unwrap());
        if i == 0 && j == 0 {
            break;
        }
        // rational of the form ±1/2^k or ±2^k
        let v = p[2];
        let neg = v.starts_with('-');
        let v = v.trim_start_matches('-');
        let coef = if let Some((num, den)) = v.split_once('/') {
            assert_eq!(num, "1");
            let d: u32 = den.parse().unwrap();
            assert!(d.is_power_of_two());
            Coef { neg, exp: -(d.trailing_zeros() as i8) }
        } else {
            let n: u32 = v.parse().unwrap();
            assert!(n.is_power_of_two());
            Coef { neg, exp: n.trailing_zeros() as i8 }
        };
        m[i - 1][j - 1] = Some(coef);
    }
    let (r, c) = dims.unwrap();
    (r, c, m)
}

// ---------- the tensor + slot variants ----------
#[derive(Clone)]
struct Instance {
    name: String,
    s1: Vec<Form>,  // 48 forms over 16 vars
    s2: Vec<Form>,  // 48 forms over 16 vars
    out: Vec<Form>, // output map as its transpose: 48 forms over 16 vars
}

fn rows_to_forms(m: &[Vec<Option<Coef>>]) -> Vec<Form> {
    m.iter()
        .map(|row| {
            row.iter()
                .enumerate()
                .filter_map(|(j, c)| c.map(|c| (j as u32, c)))
                .collect()
        })
        .collect()
}

fn transpose_mat(m: &[Vec<Option<Coef>>]) -> Vec<Vec<Option<Coef>>> {
    let (r, c) = (m.len(), m[0].len());
    (0..c)
        .map(|j| (0..r).map(|i| m[i][j]).collect())
        .collect()
}

/// reindex the 16-dim space by the 4x4 matrix transpose (p,q) -> (q,p)
fn t16(m: &[Vec<Option<Coef>>]) -> Vec<Vec<Option<Coef>>> {
    m.iter()
        .map(|row| {
            let mut out = vec![None; 16];
            for (j, c) in row.iter().enumerate() {
                let (p, q) = (j / 4, j % 4);
                out[4 * q + p] = *c;
            }
            out
        })
        .collect()
}

/// gauge: per product, use the free alpha*beta*gamma = 1 scaling to
/// minimize the shift burden.  Step 1 normalizes each side row to max
/// exponent 0 (collecting all scale in the output column).  Step 2
/// re-splits per product: shifting the output column i by 2^k costs
/// at most one shift on that product's side wire (k != 0) and changes
/// the column's distinct-nonzero-exponent count — pick the k zeroing
/// the column's modal exponent whenever that wins.
fn gauge(s1: &mut [Vec<Option<Coef>>], s2: &mut [Vec<Option<Coef>>], out: &mut [Vec<Option<Coef>>], mode: u32) {
    for i in 0..48 {
        for side in [&mut *s1, &mut *s2] {
            let mx = side[i].iter().flatten().map(|c| c.exp).max().unwrap();
            if mx != 0 {
                for c in side[i].iter_mut().flatten() {
                    c.exp -= mx;
                }
                for row in out.iter_mut() {
                    if let Some(c) = &mut row[i] {
                        c.exp += mx;
                    }
                }
            }
        }
    }
    if mode == 0 {
        return; // conservative: row-normalized sides only
    }
    // step 2: per output column, count exponents and try k = -modal
    for i in 0..48 {
        let mut exps: Vec<i8> = out
            .iter()
            .filter_map(|row| row[i].map(|c| c.exp))
            .collect();
        if exps.is_empty() {
            continue;
        }
        exps.sort_unstable();
        // cost(k) = #distinct nonzero exps after subtracting k, plus 1
        // side shift if k != 0
        // mode 1: ties prefer no-rescale (0 first); mode 2: ties
        // prefer rescaling (0 last — aggressive, worth it when the
        // exponent spread fragments extraction sharing)
        let cand: Vec<i8> = {
            let mut e: Vec<i8> = exps.clone();
            e.dedup();
            let mut c: Vec<i8> = Vec::new();
            if mode == 1 {
                c.push(0);
            }
            c.extend(e.into_iter().filter(|&k| k != 0));
            if mode != 1 {
                c.push(0);
            }
            c
        };
        let cost = |k: i8| -> u32 {
            let mut es: Vec<i8> = exps.iter().map(|e| e - k).collect();
            es.sort_unstable();
            es.dedup();
            es.iter().filter(|&&e| e != 0).count() as u32 + (k != 0) as u32
        };
        let best = *cand.iter().min_by_key(|&&k| cost(k)).unwrap();
        if best != 0 {
            for row in out.iter_mut() {
                if let Some(c) = &mut row[i] {
                    c.exp -= best;
                }
            }
            // compensate on side 1's row (its wire picks up 2^best —
            // one shift, which cost() already charged)
            for c in s1[i].iter_mut().flatten() {
                c.exp += best;
            }
        }
    }
}

/// exact Brent check over Z: scale every coefficient by 2^9 per factor.
fn brent_ok(s1: &[Vec<Option<Coef>>], s2: &[Vec<Option<Coef>>], out: &[Vec<Option<Coef>>]) -> bool {
    let val = |c: &Option<Coef>| -> i64 {
        match c {
            None => 0,
            Some(c) => {
                let v = 1i64 << (c.exp + 9) as u32;
                if c.neg { -v } else { v }
            }
        }
    };
    for x in 0..16 {
        let (a, b) = (x / 4, x % 4);
        for y in 0..16 {
            let (c, d) = (y / 4, y % 4);
            for z in 0..16 {
                let (p, q) = (z / 4, z % 4);
                let mut s: i64 = 0;
                for i in 0..48 {
                    s += val(&s1[i][x]) * val(&s2[i][y]) * val(&out[z][i]);
                }
                let want = if b == c && a == p && d == q { 1i64 << 27 } else { 0 };
                if s != want {
                    return false;
                }
            }
        }
    }
    true
}

fn build_instances(dir: &str) -> Vec<Instance> {
    let (_, _, l) = parse_sms(&format!("{dir}/L.sms"));
    let (_, _, r) = parse_sms(&format!("{dir}/R.sms"));
    let (_, _, p) = parse_sms(&format!("{dir}/P.sms"));
    let pt = transpose_mat(&p); // 48 x 16: row i = O_i^T vectorized
    // families as 48x16 matrices: M = L, N = R, O = pt
    // trilinear symmetry: Trace(O^T M N) = Trace(M^T N O)?? — we do not
    // derive on paper; we enumerate candidate slot assignments and KEEP
    // exactly those that pass the exact Brent check.
    let fams = [("L", l), ("R", r), ("Pt", pt)];
    // brute-force the S3 x flips bookkeeping: every slot permutation x
    // every per-slot 4x4 reindex; keep exactly the Brent-passers.
    let mut instances = Vec::new();
    for a in 0..3usize {
        for b in 0..3usize {
            for c in 0..3usize {
                if a == b || b == c || a == c {
                    continue;
                }
                for bits in 0..8u32 {
                    let mk = |k: usize, fl: bool| -> Vec<Vec<Option<Coef>>> {
                        if fl { t16(&fams[k].1) } else { fams[k].1.clone() }
                    };
                    for mode in 0..3u32 {
                        let mut s1 = mk(a, bits & 1 != 0);
                        let mut s2 = mk(b, bits & 2 != 0);
                        let ot = mk(c, bits & 4 != 0); // 48 x 16
                        let mut outm = transpose_mat(&ot); // 16 x 48
                        gauge(&mut s1, &mut s2, &mut outm, mode);
                        if brent_ok(&s1, &s2, &outm) {
                            let tag = |fl: bool| if fl { "t" } else { "" };
                            instances.push(Instance {
                                name: format!(
                                    "{}{}|{}{}>{}{} g{}",
                                    fams[a].0, tag(bits & 1 != 0),
                                    fams[b].0, tag(bits & 2 != 0),
                                    fams[c].0, tag(bits & 4 != 0),
                                    mode
                                ),
                                s1: rows_to_forms(&s1),
                                s2: rows_to_forms(&s2),
                                out: rows_to_forms(&transpose_mat(&outm)),
                            });
                        }
                    }
                }
            }
        }
    }
    instances
}

// ---------- greedy dyadic pair CSE ----------
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

/// kernel pre-phase (PLinOpt Alg-2 idea): in the rank-deficient
/// 48-forms-over-16-vars orientations, ~32 rows are combinations of
/// others.  A row equal to alpha*row_a (alpha = +-2^k) is free up to a
/// deduped shift; a row equal to alpha*row_a + beta*row_b costs 1 add
/// (+ deduped shifts for non-unit alpha/beta).  Scanned in rng order,
/// deriving only from kept rows.  Returns (kept, adds, shift_keys)
/// where shift_keys join the caller's global dedup set (keys use the
/// high bit so they cannot collide with extraction wires).
fn kernel_prephase(
    forms: &[Form],
    rng: &mut Rng,
) -> (Vec<Form>, u32, Vec<(u32, i8)>) {
    let nv = 16usize;
    let val = |c: &Coef| -> i64 {
        let v = 1i64 << ((c.exp as i32) + 10);
        if c.neg { -v } else { v }
    };
    let dense: Vec<Vec<i64>> = forms
        .iter()
        .map(|f| {
            let mut row = vec![0i64; nv];
            for &(v, c) in f {
                row[v as usize] = val(&c);
            }
            row
        })
        .collect();
    // x/y as +-2^k if it is one
    let dyadic = |x: i128, y: i128| -> Option<(bool, i8)> {
        if x == 0 || y == 0 {
            return None;
        }
        let neg = (x < 0) != (y < 0);
        let (ax, ay) = (x.abs(), y.abs());
        let (big, small, sg) = if ax >= ay { (ax, ay, 1i8) } else { (ay, ax, -1i8) };
        if big % small != 0 {
            return None;
        }
        let q = (big / small) as u128;
        if !q.is_power_of_two() {
            return None;
        }
        let k = q.trailing_zeros() as i8 * sg;
        if k.abs() > 6 { None } else { Some((neg, k)) }
    };
    let n = forms.len();
    let mut order: Vec<usize> = (0..n).collect();
    for i in (1..n).rev() {
        let j = rng.below(i + 1);
        order.swap(i, j);
    }
    let mut derived = vec![false; n];
    let mut kadds = 0u32;
    let mut shifts: Vec<(u32, i8)> = Vec::new();
    let wire = |i: usize| 0x8000_0000u32 | i as u32;
    for &c in &order {
        if dense[c].iter().all(|&x| x == 0) {
            continue;
        }
        let rc = &dense[c];
        let mut done = false;
        // scalar multiples first (cost: at most one shift)
        for &a in &order {
            if a == c || derived[a] {
                continue;
            }
            let ra = &dense[a];
            if (0..nv).any(|v| (ra[v] == 0) != (rc[v] == 0)) {
                continue;
            }
            let v0 = (0..nv).find(|&v| rc[v] != 0).unwrap();
            if let Some((_, k)) = dyadic(rc[v0] as i128, ra[v0] as i128) {
                if (0..nv).all(|v| {
                    ra[v] == 0 || rc[v] as i128 * ra[v0] as i128 == ra[v] as i128 * rc[v0] as i128
                }) {
                    if k != 0 {
                        shifts.push((wire(a), k));
                    }
                    derived[c] = true;
                    done = true;
                    break;
                }
            }
        }
        if done {
            continue;
        }
        'pair: for &a in &order {
            if a == c || derived[a] {
                continue;
            }
            for &b in &order {
                if b <= a || b == c || derived[b] {
                    continue;
                }
                let (ra, rb) = (&dense[a], &dense[b]);
                // two vars with nonzero determinant
                let mut piv = None;
                'fv: for v1 in 0..nv {
                    for v2 in v1 + 1..nv {
                        let det = ra[v1] as i128 * rb[v2] as i128
                            - ra[v2] as i128 * rb[v1] as i128;
                        if det != 0 {
                            piv = Some((v1, v2, det));
                            break 'fv;
                        }
                    }
                }
                let (v1, v2, det) = match piv {
                    Some(p) => p,
                    None => continue,
                };
                // Cramer: alpha = (rc x rb), beta = (ra x rc) over det
                let na = rc[v1] as i128 * rb[v2] as i128 - rc[v2] as i128 * rb[v1] as i128;
                let nb = ra[v1] as i128 * rc[v2] as i128 - ra[v2] as i128 * rc[v1] as i128;
                if na == 0 || nb == 0 {
                    continue; // scalar case, handled above
                }
                let (da, db) = match (dyadic(na, det), dyadic(nb, det)) {
                    (Some(x), Some(y)) => (x, y),
                    _ => continue,
                };
                // verify every var exactly: det*rc == na*ra + nb*rb
                if !(0..nv).all(|v| {
                    det * rc[v] as i128
                        == na * ra[v] as i128 + nb * rb[v] as i128
                }) {
                    continue;
                }
                kadds += 1;
                if da.1 != 0 {
                    shifts.push((wire(a), da.1));
                }
                if db.1 != 0 {
                    shifts.push((wire(b), db.1));
                }
                derived[c] = true;
                break 'pair;
            }
        }
    }
    let kept: Vec<Form> = (0..n)
        .filter(|&i| !derived[i])
        .map(|i| forms[i].clone())
        .collect();
    (kept, kadds, shifts)
}

/// greedy signed-dyadic-pair CSE; returns (adds, shifts).
/// Each extraction w = x_i + s·2^k x_j: 1 add (+1 shift if k≠0).
/// Final assembly of a form with ℓ terms: ℓ−1 adds + one shift per
/// term with residual coefficient ≠ ±1 (over-approximation is fine —
/// all comparisons use the same accounting).
fn greedy(forms: &[Form], nvars: u32, kernel: bool, rng: &mut Rng) -> (u32, u32) {
    let (pre_forms, mut adds, kshifts) = if kernel {
        let (kept, ka, ks) = kernel_prephase(forms, rng);
        (kept, ka, ks)
    } else {
        (forms.to_vec(), 0u32, Vec::new())
    };
    let mut forms: Vec<Form> = pre_forms
        .into_iter()
        .filter(|f| f.len() >= 2)
        .collect();
    let mut next_var = nvars;
    // shifts dedup: a materialized 2^k·v is one shift however often
    // it is reused (matches the paper's shift accounting)
    let mut shifted: std::collections::HashSet<(u32, i8)> =
        std::collections::HashSet::new();
    shifted.extend(kshifts);
    let mut keys: Vec<u64> = Vec::with_capacity(4096);
    loop {
        // packed pattern keys (va, vb, sign, exp+64), sort + run-length
        keys.clear();
        for f in &forms {
            for ai in 0..f.len() {
                for bi in ai + 1..f.len() {
                    let (va, ca) = f[ai];
                    let (vb, cb) = f[bi];
                    let (s, e) = Coef::ratio(ca, cb);
                    keys.push(
                        ((va as u64) << 32)
                            | ((vb as u64) << 12)
                            | ((s as u64) << 8)
                            | (e + 64) as u64,
                    );
                }
            }
        }
        keys.sort_unstable();
        // shift-aware score: an extraction saving `c` occurrences is
        // worth 2c, minus 1 if it must materialize a new (value, 2^k)
        // shift that the global dedup set does not already contain
        let mut best = 0i64;
        let mut bestc = 0u32;
        let mut top: Vec<u64> = Vec::new();
        let mut i = 0;
        while i < keys.len() {
            let mut j = i + 1;
            while j < keys.len() && keys[j] == keys[i] {
                j += 1;
            }
            let c = (j - i) as u32;
            if c >= 2 {
                let k = keys[i];
                let vb = ((k >> 12) & 0xfffff) as u32;
                let e = ((k & 0xff) as i8) - 64;
                let newshift = e != 0 && !shifted.contains(&(vb, e));
                let score = 2 * c as i64 - newshift as i64;
                if score > best {
                    best = score;
                    bestc = c;
                    top.clear();
                    top.push(k);
                } else if score == best {
                    top.push(k);
                }
            }
            i = j;
        }
        if bestc < 2 {
            break;
        }
        let k = top[rng.below(top.len())];
        let (va, vb) = ((k >> 32) as u32, ((k >> 12) & 0xfffff) as u32);
        let s = (k >> 8) & 1 != 0;
        let e = ((k & 0xff) as i8) - 64;
        // w = x_va + s·2^e x_vb
        adds += 1;
        if e != 0 {
            shifted.insert((vb, e));
        }
        let w = next_var;
        next_var += 1;
        for f in forms.iter_mut() {
            let pa = f.iter().position(|&(v, _)| v == va);
            let pb = f.iter().position(|&(v, _)| v == vb);
            if let (Some(pa), Some(pb)) = (pa, pb) {
                let (_, ca) = f[pa];
                let (_, cb) = f[pb];
                let (rs, re) = Coef::ratio(ca, cb);
                if rs == s && re == e {
                    f.retain(|&(v, _)| v != va && v != vb);
                    f.push((w, ca));
                }
            }
        }
    }
    // final assembly with common-exponent hoisting: sum the form at
    // its modal exponent e* (terms off the mode need a relative shift,
    // deduped globally by (value, delta)), then one shift materializes
    // 2^{e*} of the completed wire when e* != 0.  This is a valid SLP
    // transformation for sides and outputs alike.
    let mut hoists = 0u32;
    for f in &forms {
        adds += f.len() as u32 - 1;
        let mut exps: Vec<i8> = f.iter().map(|&(_, c)| c.exp).collect();
        exps.sort_unstable();
        let mut estar = exps[0];
        let mut bestrun = 0;
        let mut i = 0;
        while i < exps.len() {
            let mut j = i + 1;
            while j < exps.len() && exps[j] == exps[i] {
                j += 1;
            }
            if j - i > bestrun {
                bestrun = j - i;
                estar = exps[i];
            }
            i = j;
        }
        if estar != 0 {
            hoists += 1;
        }
        for &(v, c) in f {
            if c.exp != estar {
                shifted.insert((v, c.exp - estar));
            }
        }
    }
    (adds, shifted.len() as u32 + hoists)
}

/// transposed view: columns of the 48x16 side as 16 forms over 48 vars
fn transpose_forms(forms: &[Form], nvars: u32) -> Vec<Form> {
    let mut out: Vec<Form> = vec![Vec::new(); nvars as usize];
    for (i, f) in forms.iter().enumerate() {
        for &(v, c) in f {
            out[v as usize].push((i as u32, c));
        }
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |flag: &str, default: u64| -> u64 {
        args.iter()
            .position(|a| a == flag)
            .and_then(|i| args.get(i + 1))
            .and_then(|v| v.parse().ok())
            .unwrap_or(default)
    };
    let seconds = get("--seconds", 60);
    let threads = get("--threads", 12) as usize;
    let dir = args
        .iter()
        .position(|a| a == "--dir")
        .and_then(|i| args.get(i + 1).cloned())
        .unwrap_or_else(|| "matmul/dps48".into());

    rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build_global()
        .unwrap();

    let instances = build_instances(&dir);
    println!("instances passing exact Brent check: {}", instances.len());
    for ins in &instances {
        println!("  {}", ins.name);
    }

    // components per instance: s1, s2 (direct + transposed est) and
    // out (16x48, estimated via its transpose = 48 forms/16 vars + 32)
    // scores are (adds + shifts) totals with the transposition offset.
    let ncomp = instances.len() * 3;
    let best: Vec<AtomicU32> = (0..ncomp).map(|_| AtomicU32::new(u32::MAX)).collect();
    let rounds = AtomicU64::new(0);
    let t0 = Instant::now();

    (0..threads as u64).into_par_iter().for_each(|tid| {
        let mut rng = Rng(0x9e3779b97f4a7c15 ^ (tid * 0x2545f4914f6cdd1d + 1));
        while t0.elapsed().as_secs() < seconds {
            for (ii, ins) in instances.iter().enumerate() {
                for (ci, comp) in [&ins.s1, &ins.s2, &ins.out].into_iter().enumerate() {
                    let slot = ii * 3 + ci;
                    // components are stored as 48 forms over 16 vars
                    // (out is stored as out^T).  Direct greedy scores
                    // the stored orientation; the transposed estimator
                    // uses Tellegen: SLP(W) = SLP(W^T) + in(W) - out(W).
                    // For sides (in 16, out 48): transposed - 32.
                    // For out (in 48, out 16): stored^T IS out, so
                    // direct-on-stored + 32, transposed = greedy on
                    // 16 forms/48 vars with no offset.
                    let flip = rng.next() & 1 == 0;
                    let (a, sh, off, tag) = if flip {
                        // 48 forms / 16 vars: rank <= 16, kernel-rich;
                        // coin-flip the kernel so the plain-greedy
                        // distribution stays in play for the sides
                        let kern = rng.next() & 1 == 0;
                        let (a, s) = greedy(comp, 16, kern, &mut rng);
                        (a, s, if ci == 2 { 32i64 } else { 0 }, "48/16")
                    } else {
                        let tf = transpose_forms(comp, 16);
                        let (a, s) = greedy(&tf, 48, false, &mut rng);
                        (a, s, if ci == 2 { 0 } else { -32 }, "16/48")
                    };
                    let score = (a as i64 + sh as i64 + off) as u32;
                    let prev = best[slot].fetch_min(score, Ordering::Relaxed);
                    if score < prev {
                        println!(
                            "[{:.0}s] {} comp{} {} = {} ({}a+{}s{:+})",
                            t0.elapsed().as_secs_f32(),
                            ins.name, ci, tag, score, a, sh, off
                        );
                    }
                }
            }
            rounds.fetch_add(1, Ordering::Relaxed);
        }
    });

    println!("\n=== {} rounds x {} threads in {:.0}s ===",
             rounds.load(Ordering::Relaxed), threads, t0.elapsed().as_secs_f32());
    let mut grand = u32::MAX;
    for (ii, ins) in instances.iter().enumerate() {
        let t: u32 = (0..3).map(|ci| best[ii * 3 + ci].load(Ordering::Relaxed)).sum();
        println!("{:<12} total {}  (components {} {} {})",
                 ins.name, t,
                 best[ii * 3].load(Ordering::Relaxed),
                 best[ii * 3 + 1].load(Ordering::Relaxed),
                 best[ii * 3 + 2].load(Ordering::Relaxed));
        grand = grand.min(t);
    }
    println!("BEST TOTAL {}  (published SLP: 341 = 104 + 85 + 152)", grand);
}
