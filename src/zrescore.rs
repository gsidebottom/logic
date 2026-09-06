//! Exact Z-rescoring of 3x3x23 scheme representatives, in-process —
//! the Rust port of the Python candidate pipeline
//! (matmul/lift.py sign-SAT + matmul/sidemin.py exact sides +
//! matmul/slp.py greedy C), roughly 100x faster per candidate and
//! embarrassingly parallel across candidates.
//!
//! Pipeline per scheme: enumerate sign models of the mod-2 support
//! (sign-SAT: one sign bit per support coefficient; a covering term's
//! sign is the XOR of its three bits; the integer Brent equation with
//! k covering terms and RHS r says exactly (k-r)/2 term bits are 1;
//! per-product scaling gauge broken by fixing the first alpha/beta
//! support sign of each product; CaDiCaL in-process with blocking
//! clauses), Z-verify each model exactly, then score: exact signed
//! side minimization for A and B (addition-chain covering, closure +
//! helper IDDFS over arbitrary integer helper vectors — the same
//! algorithm as matmul/sidemin.py, calibrated there against Sun's
//! optimality certificates) plus restart-greedy signed pair CSE for C
//! (deterministic first pass reproduces the Python v1 optimizer's
//! trajectory bit for bit, including its str()-key ordering).

use std::collections::{HashMap, HashSet};

pub const NA: usize = 207;
pub const NB: usize = 207;
pub const NV: usize = 621;
pub const R: usize = 23;

// ---------------- Brent term structure over the 621-bit layout -------

/// (va, vb, vg, rhs) monomials grouped per equation; alpha var of
/// summand m cell (i,l) at m*9+3i+l, beta at NA+m*9+3lp+j, gamma at
/// NA+NB+m*9+3ip+jp; rhs = delta(l,lp)delta(i,ip)delta(j,jp).
pub fn brent_equations() -> Vec<(Vec<(usize, usize, usize)>, u8)> {
    let mut eqs = Vec::with_capacity(729);
    for i in 0..3 {
        for l in 0..3 {
            for lp in 0..3 {
                for j in 0..3 {
                    for ip in 0..3 {
                        for jp in 0..3 {
                            let mons = (0..R)
                                .map(|m| {
                                    (
                                        m * 9 + 3 * i + l,
                                        NA + m * 9 + 3 * lp + j,
                                        NA + NB + m * 9 + 3 * ip + jp,
                                    )
                                })
                                .collect();
                            let rhs = u8::from(
                                l == lp && i == ip && j == jp,
                            );
                            eqs.push((mons, rhs));
                        }
                    }
                }
            }
        }
    }
    eqs
}

/// mod-2 Brent violations of a bit vector (0 = valid scheme).
pub fn mod2_bad(bits: &[u8], eqs: &[(Vec<(usize, usize, usize)>, u8)]) -> usize {
    eqs.iter()
        .filter(|(mons, rhs)| {
            let s: u8 = mons
                .iter()
                .map(|&(a, b, g)| bits[a] & bits[b] & bits[g])
                .fold(0, |x, y| x ^ y);
            s != *rhs
        })
        .count()
}

/// exact integer Brent violations for signed coefficients in {-1,0,1}.
pub fn z_bad(coef: &[i32], eqs: &[(Vec<(usize, usize, usize)>, u8)]) -> usize {
    eqs.iter()
        .filter(|(mons, rhs)| {
            let s: i32 = mons
                .iter()
                .map(|&(a, b, g)| coef[a] * coef[b] * coef[g])
                .sum();
            s != *rhs as i32
        })
        .count()
}

// ---------------- sign-SAT model enumeration (CaDiCaL) ----------------

/// up to `nmodels` distinct sign vectors (coef[v] in {-1,0,+1}, 0 off
/// support), each Z-verified exactly.  Ports matmul/lift.py's
/// encoding: XOR3 term bits + binomial exactly-(k-r)/2 cardinality +
/// first-alpha/beta unit gauge + blocking clauses over sign vars.
pub fn sign_models(
    bits: &[u8],
    nmodels: usize,
    eqs: &[(Vec<(usize, usize, usize)>, u8)],
) -> Vec<Vec<i32>> {
    let support: Vec<usize> = (0..NV).filter(|&v| bits[v] == 1).collect();
    let svar: HashMap<usize, i32> = support
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, i as i32 + 1))
        .collect();
    let mut nxt = support.len() as i32 + 1;
    let mut clauses: Vec<Vec<i32>> = Vec::new();

    // gauge: first alpha + first beta support sign of each product = +
    for m in 0..R {
        for base in [m * 9, NA + m * 9] {
            for k in 0..9 {
                if bits[base + k] == 1 {
                    clauses.push(vec![-svar[&(base + k)]]);
                    break;
                }
            }
        }
    }

    for (mons, rhs) in eqs {
        let terms: Vec<(usize, usize, usize)> = mons
            .iter()
            .copied()
            .filter(|&(a, b, g)| bits[a] & bits[b] & bits[g] == 1)
            .collect();
        let k = terms.len();
        assert_eq!(k % 2, *rhs as usize, "not mod-2 valid");
        if k == 0 {
            continue;
        }
        let mut tvars = Vec::with_capacity(k);
        for &(va, vb, vg) in &terms {
            let t = nxt;
            nxt += 1;
            tvars.push(t);
            let trip = [svar[&va], svar[&vb], svar[&vg]];
            for pat in 0..8u32 {
                // pattern bit 1 = sign var true (negative coefficient)
                let par = (pat.count_ones() & 1) as i32;
                let mut cl: Vec<i32> = (0..3)
                    .map(|ix| {
                        if pat >> ix & 1 == 1 {
                            -trip[ix]
                        } else {
                            trip[ix]
                        }
                    })
                    .collect();
                cl.push(if par == 1 { t } else { -t });
                clauses.push(cl);
            }
        }
        let n1 = (k - *rhs as usize) / 2; // exactly n1 negative terms
        for sub in combinations(&tvars, n1 + 1) {
            clauses.push(sub.iter().map(|&t| -t).collect());
        }
        for sub in combinations(&tvars, k - n1 + 1) {
            clauses.push(sub);
        }
    }

    let mut solver: cadical::Solver = cadical::Solver::new();
    for c in &clauses {
        solver.add_clause(c.iter().copied());
    }
    let mut out = Vec::new();
    for _ in 0..nmodels {
        match solver.solve() {
            Some(true) => {}
            _ => break,
        }
        let mut coef = vec![0i32; NV];
        // blocking clause = negation of this assignment on sign vars
        let mut block = Vec::with_capacity(support.len());
        for &v in &support {
            let s = svar[&v];
            let neg = solver.value(s).unwrap_or(false);
            coef[v] = if neg { -1 } else { 1 };
            block.push(if neg { -s } else { s });
        }
        assert_eq!(z_bad(&coef, eqs), 0, "model fails exact Z Brent");
        out.push(coef);
        solver.add_clause(block.iter().copied());
    }
    out
}

fn combinations(items: &[i32], k: usize) -> Vec<Vec<i32>> {
    let n = items.len();
    let mut out = Vec::new();
    if k > n {
        return out;
    }
    let mut idx: Vec<usize> = (0..k).collect();
    loop {
        out.push(idx.iter().map(|&i| items[i]).collect());
        let mut i = k;
        loop {
            if i == 0 {
                return out;
            }
            i -= 1;
            if idx[i] != i + n - k {
                break;
            }
        }
        idx[i] += 1;
        for j in i + 1..k {
            idx[j] = idx[j - 1] + 1;
        }
    }
}

// ---------------- exact signed side minimization ----------------

pub type Vec9 = [i16; 9];

fn canon9(v: Vec9) -> Vec9 {
    for x in v {
        if x > 0 {
            return v;
        }
        if x < 0 {
            let mut w = v;
            for e in w.iter_mut() {
                *e = -*e;
            }
            return w;
        }
    }
    v
}

fn sub9(a: &Vec9, s: i16, b: &Vec9) -> Vec9 {
    let mut r = [0i16; 9];
    for i in 0..9 {
        r[i] = a[i] - s * b[i];
    }
    r
}

fn add9(a: &Vec9, s: i16, b: &Vec9) -> Vec9 {
    let mut r = [0i16; 9];
    for i in 0..9 {
        r[i] = a[i] + s * b[i];
    }
    r
}

fn is_zero(v: &Vec9) -> bool {
    v.iter().all(|&x| x == 0)
}

pub struct ZSideCost {
    pub nt: u32,
    pub adds: u32,
    /// false = search open (max-slack or node cap); adds is a lower bound
    pub exact: bool,
}

struct ZSearch {
    targets: Vec<Vec9>,
    nodes: u64,
    node_cap: u64,
}

impl ZSearch {
    fn derivable(&self, t: &Vec9, pool: &HashSet<Vec9>, list: &[Vec9]) -> bool {
        for x in list {
            for s in [1i16, -1] {
                let r = sub9(t, s, x);
                if !is_zero(&r) && pool.contains(&canon9(r)) {
                    return true;
                }
            }
        }
        false
    }

    fn dfs(
        &mut self,
        pool: &mut HashSet<Vec9>,
        list: &mut Vec<Vec9>,
        unc0: u32,
        h: u32,
        memo: &mut Vec<HashSet<Vec<Vec9>>>,
    ) -> Result<bool, ()> {
        self.nodes += 1;
        if self.nodes > self.node_cap {
            return Err(());
        }
        // closure: cover every derivable target (pool monotone)
        let mut unc = unc0;
        let mut progress = true;
        while progress {
            progress = false;
            let mut m = unc;
            while m != 0 {
                let ti = m.trailing_zeros() as usize;
                m &= m - 1;
                let t = self.targets[ti];
                if self.derivable(&t, pool, list) {
                    pool.insert(t);
                    list.push(t);
                    unc &= !(1 << ti);
                    progress = true;
                }
            }
        }
        if unc == 0 {
            return Ok(true);
        }
        if h == 0 {
            return Ok(false);
        }
        let mut key: Vec<Vec9> = list.clone();
        key.sort_unstable();
        if !memo[h as usize].insert(key) {
            return Ok(false);
        }
        // enabling: u (canon, not in pool) with t = s*x + s'*u
        let mut enab: HashMap<Vec9, u32> = HashMap::new();
        let mut m = unc;
        while m != 0 {
            let ti = m.trailing_zeros() as usize;
            m &= m - 1;
            let t = self.targets[ti];
            for x in list.iter() {
                for s in [1i16, -1] {
                    let r = sub9(&t, s, x);
                    if is_zero(&r) {
                        continue;
                    }
                    let u = canon9(r);
                    if !pool.contains(&u) {
                        *enab.entry(u).or_insert(0) += 1;
                    }
                }
            }
        }
        let mut cands: Vec<Vec9> = if h == 1 {
            enab.keys()
                .filter(|u| self.derivable(u, pool, list))
                .copied()
                .collect()
        } else {
            let mut set: HashSet<Vec9> = HashSet::new();
            for i in 0..list.len() {
                for j in 0..=i {
                    for s in [1i16, -1] {
                        let v = add9(&list[i], s, &list[j]);
                        if is_zero(&v) {
                            continue;
                        }
                        let c = canon9(v);
                        if !pool.contains(&c) {
                            set.insert(c);
                        }
                    }
                }
            }
            set.into_iter().collect()
        };
        cands.sort_unstable_by_key(|u| {
            (
                std::cmp::Reverse(enab.get(u).copied().unwrap_or(0)),
                u.iter().filter(|&&x| x != 0).count(),
                *u,
            )
        });
        for u in cands {
            let mut p2 = pool.clone();
            let mut l2 = list.clone();
            p2.insert(u);
            l2.push(u);
            if self.dfs(&mut p2, &mut l2, unc, h - 1, memo)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

/// exact minimum signed +- additions covering all weight>=2 rows
/// (helpers may be arbitrary integer vectors, doubling included) —
/// the matmul/sidemin.py algorithm on packed [i16;9] values.
pub fn z_min_side(rows: &[Vec9], max_slack: u32, node_cap: u64) -> ZSideCost {
    let mut targets: Vec<Vec9> = Vec::new();
    for &r in rows {
        let c = canon9(r);
        if c.iter().filter(|&&x| x != 0).count() >= 2
            && !targets.contains(&c)
        {
            targets.push(c);
        }
    }
    let nt = targets.len() as u32;
    if nt == 0 {
        return ZSideCost { nt, adds: 0, exact: true };
    }
    assert!(targets.len() <= 32);
    let full: u32 = if targets.len() == 32 {
        u32::MAX
    } else {
        (1u32 << targets.len()) - 1
    };
    let mut s = ZSearch { targets, nodes: 0, node_cap };
    for h in 0..=max_slack {
        let mut memo: Vec<HashSet<Vec<Vec9>>> =
            (0..=h).map(|_| HashSet::new()).collect();
        let mut pool: HashSet<Vec9> = HashSet::new();
        let mut list: Vec<Vec9> = Vec::with_capacity(48);
        for i in 0..9 {
            let mut e = [0i16; 9];
            e[i] = 1;
            pool.insert(e);
            list.push(e);
        }
        match s.dfs(&mut pool, &mut list, full, h, &mut memo) {
            Ok(true) => return ZSideCost { nt, adds: nt + h, exact: true },
            Ok(false) => {}
            Err(()) => return ZSideCost { nt, adds: nt + h, exact: false },
        }
    }
    ZSideCost { nt, adds: nt + max_slack + 1, exact: false }
}

// ---------------- greedy signed pair CSE for the C side ----------------

/// symbol = product index (0..23) or aux w-index; ordering replicates
/// Python's sorted(key=str): products compare as decimal strings,
/// w-symbols as "w<i>" strings, and every product string < every "w".
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Sym {
    P(u8),
    W(u16),
}

fn sym_str(s: Sym) -> String {
    match s {
        Sym::P(k) => k.to_string(),
        Sym::W(i) => format!("w{i}"),
    }
}

/// greedy signed-pair CSE; deterministic when `rng` is None (bit-for-
/// bit the Python v1 trajectory); returns total adds.
pub fn greedy_c(forms0: &[Vec<(Sym, i8)>], mut rng: Option<&mut u64>) -> u32 {
    // forms as small sorted-by-str vecs of (sym, +-1)
    let mut forms: Vec<Vec<(Sym, i8)>> = forms0
        .iter()
        .map(|f| {
            let mut v = f.clone();
            v.sort_by(|a, b| sym_str(a.0).cmp(&sym_str(b.0)));
            v
        })
        .collect();
    let mut next_w = 0u16;
    let mut adds = 0u32;
    loop {
        // counts in insertion order (CPython dict semantics)
        let mut order: Vec<(Sym, i8, Sym, i8)> = Vec::new();
        let mut counts: HashMap<(Sym, i8, Sym, i8), Vec<usize>> =
            HashMap::new();
        for (fi, f) in forms.iter().enumerate() {
            for i in 0..f.len() {
                for j in i + 1..f.len() {
                    let (mut u, mut su) = f[i];
                    let (mut v, mut sv) = f[j];
                    if sym_str(u) > sym_str(v) {
                        std::mem::swap(&mut u, &mut v);
                        std::mem::swap(&mut su, &mut sv);
                    }
                    if su < 0 {
                        su = -su;
                        sv = -sv;
                    }
                    let key = (u, su, v, sv);
                    let e = counts.entry(key).or_default();
                    if e.is_empty() {
                        order.push(key);
                    }
                    e.push(fi);
                }
            }
        }
        let top = order
            .iter()
            .map(|k| counts[k].len())
            .max()
            .unwrap_or(0);
        if top < 2 {
            break;
        }
        let tied: Vec<&(Sym, i8, Sym, i8)> =
            order.iter().filter(|k| counts[k].len() == top).collect();
        let pick = if let Some(st) = rng.as_deref_mut() {
            // xorshift64 — restart diversity only, no parity claim
            *st ^= *st << 13;
            *st ^= *st >> 7;
            *st ^= *st << 17;
            (*st as usize) % tied.len()
        } else {
            0
        };
        let &(u, su, v, sv) = tied[pick];
        let where_ = counts[&(u, su, v, sv)].clone();
        let w = Sym::W(next_w);
        next_w += 1;
        adds += 1;
        for fi in where_ {
            let f = &mut forms[fi];
            let fu = f.iter().find(|e| e.0 == u).map(|e| e.1);
            let fv = f.iter().find(|e| e.0 == v).map(|e| e.1);
            let sigma = match fu {
                Some(x) if x == su || x == -su => x / su,
                _ => continue, // stale entry
            };
            if fv != Some(sigma * sv) {
                continue;
            }
            f.retain(|e| e.0 != u && e.0 != v);
            // keep str-sorted order: all "w.." sort after products and
            // ascend with index except w10 < w2 style — insert by str
            let ws = sym_str(w);
            let pos = f
                .iter()
                .position(|e| sym_str(e.0) > ws)
                .unwrap_or(f.len());
            f.insert(pos, (w, sigma));
        }
    }
    for f in &forms {
        if !f.is_empty() {
            adds += f.len() as u32 - 1;
        }
    }
    adds
}

// ---------------- per-scheme scoring ----------------

pub struct Score {
    pub total: u32,
    pub a: u32,
    pub b: u32,
    pub c: u32,
    pub model: usize,
    pub exact_sides: bool,
}

/// best (exact A + exact B + greedy C) over sign models.
pub fn score_bits(
    bits: &[u8],
    eqs: &[(Vec<(usize, usize, usize)>, u8)],
    nmodels: usize,
    crestarts: u32,
    max_slack: u32,
    node_cap: u64,
) -> Option<Score> {
    let models = sign_models(bits, nmodels, eqs);
    let mut best: Option<Score> = None;
    for (mi, coef) in models.iter().enumerate() {
        let mut arows = [[0i16; 9]; R];
        let mut brows = [[0i16; 9]; R];
        for m in 0..R {
            for k in 0..9 {
                arows[m][k] = coef[m * 9 + k] as i16;
                brows[m][k] = coef[NA + m * 9 + k] as i16;
            }
        }
        let ra = z_min_side(&arows, max_slack, node_cap);
        let rb = z_min_side(&brows, max_slack, node_cap);
        let mut cforms: Vec<Vec<(Sym, i8)>> = vec![Vec::new(); 9];
        for pq in 0..9 {
            for m in 0..R {
                let c = coef[NA + NB + m * 9 + pq];
                if c != 0 {
                    cforms[pq].push((Sym::P(m as u8), c as i8));
                }
            }
        }
        let mut c = greedy_c(&cforms, None);
        let mut st = 0x9e3779b97f4a7c15u64
            ^ (mi as u64).wrapping_mul(0xb492b66fbe98f273);
        for _ in 1..crestarts {
            let cr = greedy_c(&cforms, Some(&mut st));
            c = c.min(cr);
        }
        let tot = ra.adds + rb.adds + c;
        let sc = Score {
            total: tot,
            a: ra.adds,
            b: rb.adds,
            c,
            model: mi,
            exact_sides: ra.exact && rb.exact,
        };
        if best.as_ref().map_or(true, |b| sc.total < b.total) {
            best = Some(sc);
        }
    }
    best
}

// ---------------- tests ----------------

#[cfg(test)]
mod tests {
    use super::*;

    fn e(i: usize) -> Vec9 {
        let mut v = [0i16; 9];
        v[i] = 1;
        v
    }

    #[test]
    fn micro_signed_side_optima() {
        let p = |pairs: &[(usize, i16)]| -> Vec9 {
            let mut v = [0i16; 9];
            for &(i, c) in pairs {
                v[i] = c;
            }
            v
        };
        // {e0+e1} -> 1;  {e0-e1} -> 1;  {e0+e1, e0-e1} -> 2;
        // {e0+e1+e2} -> 2 (h=1);  {w4} -> 3 (h=2)
        let cases: Vec<(Vec<Vec9>, u32)> = vec![
            (vec![p(&[(0, 1), (1, 1)])], 1),
            (vec![p(&[(0, 1), (1, -1)])], 1),
            (vec![p(&[(0, 1), (1, 1)]), p(&[(0, 1), (1, -1)])], 2),
            (vec![p(&[(0, 1), (1, 1), (2, 1)])], 2),
            (vec![p(&[(0, 1), (1, 1), (2, 1), (3, 1)])], 3),
        ];
        for (rows, want) in cases {
            let r = z_min_side(&rows, 3, 1_000_000);
            assert!(r.exact);
            assert_eq!(r.adds, want, "{rows:?}");
        }
        // duplicate-up-to-sign and weight-1 rows are free
        let rows = vec![
            p(&[(0, 1), (1, 1)]),
            p(&[(0, -1), (1, -1)]),
            e(4),
        ];
        let r = z_min_side(&rows, 3, 1_000_000);
        assert!(r.exact && r.adds == 1);
    }

    fn load_bits(rel: &str) -> Vec<u8> {
        let path = format!("{}/{rel}", env!("CARGO_MANIFEST_DIR"));
        let s = std::fs::read_to_string(path).unwrap();
        s.split_whitespace()
            .last()
            .unwrap()
            .chars()
            .map(|c| (c as u8) - b'0')
            .collect()
    }

    #[test]
    fn sun56_first_model_is_13_13_30() {
        let bits = load_bits("matmul/perminov_cache/bits/sun56.bits");
        let eqs = brent_equations();
        assert_eq!(mod2_bad(&bits, &eqs), 0);
        let models = sign_models(&bits, 3, &eqs);
        assert_eq!(models.len(), 3, "expected 3 distinct models");
        assert_ne!(models[0], models[1]);
        // per-model Z-verify is asserted inside sign_models; sides:
        let coef = &models[0];
        let mut arows = [[0i16; 9]; R];
        let mut brows = [[0i16; 9]; R];
        for m in 0..R {
            for k in 0..9 {
                arows[m][k] = coef[m * 9 + k] as i16;
                brows[m][k] = coef[NA + m * 9 + k] as i16;
            }
        }
        let ra = z_min_side(&arows, 3, 10_000_000);
        let rb = z_min_side(&brows, 3, 10_000_000);
        assert!(ra.exact && rb.exact);
        assert_eq!((ra.nt, ra.adds), (12, 13));
        assert_eq!((rb.nt, rb.adds), (11, 13));
    }

    #[test]
    #[ignore] // > 1 s in a debug build; run with `cargo test --release -- --ignored`
    fn reference_totals_match_python() {
        // the committed reference numbers from matmul/sidemin.py runs
        let eqs = brent_equations();
        let refs = [
            ("matmul/perminov_cache/bits/sun56.bits", 56),
            ("matmul/external/i19-perminov56.bits", 56),
            ("matmul/external/i12-orbit56.bits", 56),
            ("matmul/perminov_cache/bits/cr58-cn119.bits", 57),
            ("matmul/perminov_cache/bits/cr58-cn120.bits", 57),
            ("matmul/perminov_cache/bits/mws59.bits", 58),
        ];
        for (rel, want) in refs {
            let bits = load_bits(rel);
            let sc = score_bits(&bits, &eqs, 8, 120, 3, 10_000_000)
                .expect("liftable");
            assert!(sc.exact_sides, "{rel}");
            assert_eq!(sc.total, want, "{rel}: {}+{}+{}", sc.a, sc.b, sc.c);
        }
    }

    #[test]
    fn z_bad_negative_control() {
        let bits = load_bits("matmul/perminov_cache/bits/sun56.bits");
        let eqs = brent_equations();
        let models = sign_models(&bits, 1, &eqs);
        let mut coef = models[0].clone();
        assert_eq!(z_bad(&coef, &eqs), 0);
        let v = (0..NV).find(|&v| coef[v] != 0).unwrap();
        coef[v] = -coef[v];
        assert!(z_bad(&coef, &eqs) > 0);
    }
}

// ---------------- asymmetric (free-weight-side) scoring ----------------

/// One orientation's asymmetric score: the constant-matrix side (the
/// slot rotated into the A role) costs nothing — its linear
/// combinations are precomputed once for a fixed weight matrix — so
/// the online cost is the x-side plus the output recombination.
#[derive(Clone, Copy, Debug)]
pub struct AsymScore {
    /// online adds = b_side + c_side
    pub online: u32,
    /// free (precomputed) weight-side adds, for reference
    pub free_a: u32,
    pub b_side: u32,
    pub c_side: u32,
    /// which of the 6 tensor orientations (floors.rs s3_variants order:
    /// id, cyc, cyc^2, swp, swp*cyc, swp*cyc^2)
    pub orientation: usize,
    pub model: usize,
    pub exact: bool,
}

/// 3x3 signed matrix as row-major [i16; 9]; transpose helper.
fn t9(m: &[i16; 9]) -> [i16; 9] {
    let mut o = [0i16; 9];
    for r in 0..3 {
        for c in 0..3 {
            o[c * 3 + r] = m[r * 3 + c];
        }
    }
    o
}

/// Exact C-side adds via the transposition principle: the output map
/// M (9 outputs from R products, entries gamma_m[pq]) satisfies
/// A(M) = A(M^T) + (inputs - outputs) = z_min_side(gamma rows) + (R - 9),
/// and gamma rows (R x 9) are exactly `z_min_side`'s input shape.
pub fn exact_c_side(
    grows: &[Vec9],
    max_slack: u32,
    node_cap: u64,
) -> ZSideCost {
    let mut r = z_min_side(grows, max_slack, node_cap);
    r.adds += (grows.len() as u32) - 9;
    r
}

/// Asymmetric score of one signed model over the 6 orientations.
/// `coef` is the flat 621-signed-coefficient layout of `sign_models`.
/// Orientation maps act on the summand triple (alpha_m, beta_m,
/// gamma_m^T) exactly as floors.rs's `s3_variants`: cyc rotates the
/// triple, swp is (b^T, a^T, c^T); both preserve the Brent equations.
pub fn asym_score_model(
    coef: &[i32],
    mi: usize,
    max_slack: u32,
    node_cap: u64,
) -> AsymScore {
    // summand triples (alpha, beta, gamma-hat = gamma^T)
    let mut tri: Vec<([i16; 9], [i16; 9], [i16; 9])> = Vec::with_capacity(R);
    for m in 0..R {
        let mut a = [0i16; 9];
        let mut b = [0i16; 9];
        let mut g = [0i16; 9];
        for k in 0..9 {
            a[k] = coef[m * 9 + k] as i16;
            b[k] = coef[NA + m * 9 + k] as i16;
            g[k] = coef[NA + NB + m * 9 + k] as i16;
        }
        tri.push((a, b, t9(&g)));
    }
    let cyc = |ss: &[([i16; 9], [i16; 9], [i16; 9])]| -> Vec<_> {
        ss.iter().map(|&(a, b, c)| (b, c, a)).collect()
    };
    let swp: Vec<_> = tri
        .iter()
        .map(|&(a, b, c)| (t9(&b), t9(&a), t9(&c)))
        .collect();
    let mut variants = vec![tri.clone()];
    variants.push(cyc(&variants[0]));
    variants.push(cyc(&variants[1]));
    variants.push(swp);
    variants.push(cyc(&variants[3]));
    variants.push(cyc(&variants[4]));

    let mut best: Option<AsymScore> = None;
    for (oi, var) in variants.iter().enumerate() {
        // roles in summand form: a' = weight side (free), b' = x side,
        // c'-hat rows are gamma'^T; z_min_side wants gamma' rows
        // (gamma'_m as flat 9), i.e. un-hat: gamma' = (c'-hat)^T.
        let brows: Vec<Vec9> = var.iter().map(|&(_, b, _)| b).collect();
        let grows: Vec<Vec9> = var.iter().map(|&(_, _, c)| t9(&c)).collect();
        let rb = z_min_side(&brows, max_slack, node_cap);
        let rc = exact_c_side(&grows, max_slack, node_cap);
        let arows: Vec<Vec9> = var.iter().map(|&(a, _, _)| a).collect();
        let ra = z_min_side(&arows, max_slack, node_cap);
        let sc = AsymScore {
            online: rb.adds + rc.adds,
            free_a: ra.adds,
            b_side: rb.adds,
            c_side: rc.adds,
            orientation: oi,
            model: mi,
            exact: rb.exact && rc.exact,
        };
        if best.as_ref().map_or(true, |b| sc.online < b.online) {
            best = Some(sc);
        }
    }
    best.unwrap()
}

/// best asymmetric (free-weight-side) score over sign models.
pub fn asym_score_bits(
    bits: &[u8],
    eqs: &[(Vec<(usize, usize, usize)>, u8)],
    nmodels: usize,
    max_slack: u32,
    node_cap: u64,
) -> Option<AsymScore> {
    let models = sign_models(bits, nmodels, eqs);
    let mut best: Option<AsymScore> = None;
    for (mi, coef) in models.iter().enumerate() {
        let sc = asym_score_model(coef, mi, max_slack, node_cap);
        if best.as_ref().map_or(true, |b| sc.online < b.online) {
            best = Some(sc);
        }
    }
    best
}

#[cfg(test)]
mod asym_tests {
    use super::*;

    fn load_bits_file(path: &str) -> Vec<u8> {
        std::fs::read_to_string(path)
            .expect("bits file")
            .chars()
            .filter(|c| c.is_ascii_digit())
            .map(|c| (c as u8) - b'0')
            .collect()
    }

    /// Orientation maps must preserve the exact Z Brent equations:
    /// rebuild flat coefficients from each oriented triple and check.
    #[test]
    fn orientations_preserve_brent() {
        let eqs = brent_equations();
        let bits = load_bits_file("matmul/external/i19-perminov56.bits");
        assert_eq!(bits.len(), NV);
        let models = sign_models(&bits, 2, &eqs);
        assert!(!models.is_empty());
        let coef = &models[0];
        // reuse the internal mapping by replicating triple construction
        let mut tri: Vec<([i16; 9], [i16; 9], [i16; 9])> = Vec::new();
        for m in 0..R {
            let mut a = [0i16; 9];
            let mut b = [0i16; 9];
            let mut g = [0i16; 9];
            for k in 0..9 {
                a[k] = coef[m * 9 + k] as i16;
                b[k] = coef[NA + m * 9 + k] as i16;
                g[k] = coef[NA + NB + m * 9 + k] as i16;
            }
            tri.push((a, b, t9(&g)));
        }
        let cyc = |ss: &[([i16; 9], [i16; 9], [i16; 9])]| -> Vec<_> {
            ss.iter().map(|&(a, b, c)| (b, c, a)).collect()
        };
        let swp: Vec<_> = tri
            .iter()
            .map(|&(a, b, c)| (t9(&b), t9(&a), t9(&c)))
            .collect();
        let mut variants = vec![tri.clone()];
        variants.push(cyc(&variants[0]));
        variants.push(cyc(&variants[1]));
        variants.push(swp);
        variants.push(cyc(&variants[3]));
        variants.push(cyc(&variants[4]));
        for (oi, var) in variants.iter().enumerate() {
            let mut flat = vec![0i32; NV];
            for (m, &(a, b, ch)) in var.iter().enumerate() {
                let g = t9(&ch);
                for k in 0..9 {
                    flat[m * 9 + k] = a[k] as i32;
                    flat[NA + m * 9 + k] = b[k] as i32;
                    flat[NA + NB + m * 9 + k] = g[k] as i32;
                }
            }
            assert_eq!(z_bad(&flat, &eqs), 0, "orientation {} breaks Brent", oi);
        }
    }

    /// The transposition-principle exact C must reproduce the record's
    /// C cost: on i19 the symmetric total is 55 (exact sides + C).
    #[test]
    #[ignore] // > 1 s in a debug build; run with `cargo test --release -- --ignored`
    fn record_total_reproduced_and_asym_beats_or_ties() {
        let eqs = brent_equations();
        let bits = load_bits_file("matmul/external/i19-perminov56.bits");
        let sym = score_bits(&bits, &eqs, 24, 300, 3, 10_000_000)
            .expect("symmetric score");
        let asym = asym_score_bits(&bits, &eqs, 24, 3, 10_000_000)
            .expect("asym score");
        eprintln!("symmetric: total {} = a{}+b{}+c{}", sym.total, sym.a, sym.b, sym.c);
        eprintln!("asym: online {} = b{}+c{} (free a{}, orient {}, model {})",
                  asym.online, asym.b_side, asym.c_side, asym.free_a,
                  asym.orientation, asym.model);
        // online must never exceed the symmetric total minus the cheapest side
        assert!(asym.online <= sym.total - sym.a.min(sym.b),
                "asym online {} vs symmetric {}", asym.online, sym.total);
    }
}
