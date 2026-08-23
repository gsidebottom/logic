//! spansearch — experiment (b): a symmetry-aware, linear-algebra-leaf
//! proof search for tensor-rank lower bounds of <n,n,n> over F_2.
//!
//! Reformulation. A rank-r scheme is r rank-one N x N matrices
//! v_m = alpha_m (x) beta_m (N = n^2) whose span contains the target
//! space W = span{E_pq}, where E_pq[(a,b),(c,d)] = [b=c][a=p][d=q]
//! (gamma supplies the coefficients). Since dim W = N, a rank-r scheme
//! exists iff there are t <= r - N rank-one "extenders" v_1..v_t,
//! independent modulo W, such that the rank-one elements of
//! T = W (+) <v_1..v_t> span a space containing W (then a basis of that
//! span made of rank-one elements has <= N + t <= r members).
//! So: enumerate T (v_1 up to the GL_n(F_2)^3 sandwich symmetry,
//! computed as orbit representatives; deeper extenders brute force),
//! and decide each T by linear algebra over F_2. Every T is one
//! "cube"; the leaf is Gaussian elimination. Nothing here is a
//! certificate yet — the point is to MEASURE how the number of cubes
//! grows with r compared with CDCL's x13-27 per product.
//!
//! Gate (n = 2): rank 6 must come back UNSAT (matches the certified
//! CNF result) and rank 7 SAT with a scheme that is re-verified
//! against the Brent equations from scratch.
//!
//!   spansearch --n 3 --r 11 [--max-t T] [--cap NODES] [--threads K]
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::Instant;

use rayon::prelude::*;

type M = u128; // N*N-bit matrix, bit row*N + col

struct Geo {
    n: usize,
    nn: usize, // N = n^2
}

impl Geo {
    fn row_mask(&self) -> M {
        (1u128 << self.nn) - 1
    }
    fn row(&self, m: M, i: usize) -> M {
        (m >> (i * self.nn)) & self.row_mask()
    }
    /// rank-one test: nonzero and all nonzero rows equal
    fn rank1(&self, m: M) -> bool {
        if m == 0 {
            return false;
        }
        let mut common: M = 0;
        for i in 0..self.nn {
            let r = self.row(m, i);
            if r != 0 {
                if common == 0 {
                    common = r;
                } else if r != common {
                    return false;
                }
            }
        }
        true
    }
    /// alpha (row indicator) and beta (common row) of a rank-one matrix
    fn factor(&self, m: M) -> (u32, u32) {
        let mut alpha = 0u32;
        let mut beta = 0u32;
        for i in 0..self.nn {
            let r = self.row(m, i);
            if r != 0 {
                alpha |= 1 << i;
                beta = r as u32;
            }
        }
        (alpha, beta)
    }
    fn outer(&self, alpha: u32, beta: u32) -> M {
        let mut m: M = 0;
        for i in 0..self.nn {
            if alpha >> i & 1 == 1 {
                m |= (beta as M) << (i * self.nn);
            }
        }
        m
    }
    /// W basis: E_pq for p,q in 0..n
    fn target_basis(&self) -> Vec<M> {
        let n = self.n;
        let mut ws = Vec::new();
        for p in 0..n {
            for q in 0..n {
                let mut e: M = 0;
                for a in 0..n {
                    for b in 0..n {
                        for c in 0..n {
                            for d in 0..n {
                                if b == c && a == p && d == q {
                                    let row = a * n + b;
                                    let col = c * n + d;
                                    e |= 1u128 << (row * self.nn + col);
                                }
                            }
                        }
                    }
                }
                ws.push(e);
            }
        }
        ws
    }
}

/// echelon basis over F_2 (pivot = highest set bit), insertion order kept
#[derive(Clone)]
struct Span {
    rows: Vec<M>, // reduced so that pivots are distinct
}

impl Span {
    fn new() -> Self {
        Span { rows: Vec::new() }
    }
    fn reduce(&self, mut v: M) -> M {
        for &r in &self.rows {
            let piv = 127 - r.leading_zeros();
            if v >> piv & 1 == 1 {
                v ^= r;
            }
        }
        v
    }
    /// insert; returns true if independent
    fn insert(&mut self, v: M) -> bool {
        let v = self.reduce(v);
        if v == 0 {
            return false;
        }
        // keep rows sorted by pivot descending so reduce() is a single pass
        let piv = 127 - v.leading_zeros();
        let pos = self
            .rows
            .iter()
            .position(|&r| (127 - r.leading_zeros()) < piv)
            .unwrap_or(self.rows.len());
        self.rows.insert(pos, v);
        true
    }
    fn dim(&self) -> usize {
        self.rows.len()
    }
    fn contains_all(&self, vs: &[M]) -> bool {
        vs.iter().all(|&v| self.reduce(v) == 0)
    }
}

/// GL_n(F_2) transvection generators acting on n x n bit matrices
/// (entry (i,j) = bit i*n+j): left multiply by I+E_ij adds row j to row i;
/// right multiply by I+E_ij adds column i to column j.
fn add_row(n: usize, m: u32, i: usize, j: usize) -> u32 {
    let rj = (m >> (j * n)) & ((1 << n) - 1);
    m ^ (rj << (i * n))
}
fn add_col(n: usize, m: u32, i: usize, j: usize) -> u32 {
    let mut out = m;
    for r in 0..n {
        if m >> (r * n + i) & 1 == 1 {
            out ^= 1 << (r * n + j);
        }
    }
    out
}

/// orbit representatives of rank-one matrices alpha (x) beta under the
/// sandwich group: alpha -> U^T alpha V^T, beta -> V^-T beta W^T (over F_2,
/// transvection generators are self-inverse). Union-find over all
/// (alpha, beta) pairs with the three generator families.
fn orbit_reps(g: &Geo) -> Vec<(u32, u32)> {
    let n = g.n;
    let nz = (1usize << g.nn) - 1; // nonzero alphas/betas: 1..=nz
    let idx = |a: u32, b: u32| ((a as usize) - 1) * nz + (b as usize - 1);
    let total = nz * nz;
    let mut parent: Vec<u32> = (0..total as u32).collect();
    fn find(p: &mut Vec<u32>, mut x: u32) -> u32 {
        while p[x as usize] != x {
            p[x as usize] = p[p[x as usize] as usize];
            x = p[x as usize];
        }
        x
    }
    let mut union = |p: &mut Vec<u32>, x: u32, y: u32| {
        let (rx, ry) = (find(p, x), find(p, y));
        if rx != ry {
            p[rx as usize] = ry;
        }
    };
    for a in 1..=nz as u32 {
        for b in 1..=nz as u32 {
            let x = idx(a, b) as u32;
            for i in 0..n {
                for j in 0..n {
                    if i == j {
                        continue;
                    }
                    // U: row op on alpha
                    union(&mut parent, x, idx(add_row(n, a, i, j), b) as u32);
                    // W: column op on beta
                    union(&mut parent, x, idx(a, add_col(n, b, i, j)) as u32);
                    // V (coupled): alpha -> alpha (I+E_ij), beta -> (I+E_ji) beta
                    union(&mut parent, x, idx(add_col(n, a, i, j), add_row(n, b, j, i)) as u32);
                }
            }
        }
    }
    let mut reps = Vec::new();
    for a in 1..=nz as u32 {
        for b in 1..=nz as u32 {
            let x = idx(a, b) as u32;
            if find(&mut parent, x) == x {
                reps.push((a, b));
            }
        }
    }
    reps
}

/// Decide one cube T = W (+) <ext>: do the rank-one elements of T span a
/// space containing W? Returns the rank-one basis if so.
fn decide_cube(g: &Geo, wbasis: &[M], ext: &[M]) -> Option<Vec<M>> {
    let mut tb: Vec<M> = wbasis.to_vec();
    tb.extend_from_slice(ext);
    let k = tb.len();
    let mut span = Span::new();
    let mut chosen = Vec::new();
    // enumerate all 2^k elements of T by Gray code
    let mut cur: M = 0;
    for code in 1u64..(1u64 << k) {
        let bit = code.trailing_zeros() as usize;
        cur ^= tb[bit];
        if g.rank1(cur) && span.insert(cur) {
            chosen.push(cur);
            if span.contains_all(wbasis) {
                return Some(chosen);
            }
        }
    }
    None
}

/// From a rank-one basis whose span contains W, build and VERIFY a scheme:
/// products = basis elements; gamma^(m)_{pq} = coefficient of basis m in E_pq.
fn verify_scheme(g: &Geo, wbasis: &[M], basis: &[M]) -> bool {
    let n = g.n;
    let r = basis.len();
    // express each E_pq in the basis by elimination with tracking
    let mut rows: Vec<(M, u64)> = Vec::new(); // (vector, combination mask)
    for (m, &b) in basis.iter().enumerate() {
        let mut v = b;
        let mut comb = 1u64 << m;
        for &(rv, rc) in &rows {
            let piv = 127 - rv.leading_zeros();
            if v >> piv & 1 == 1 {
                v ^= rv;
                comb ^= rc;
            }
        }
        if v == 0 {
            return false; // basis not independent
        }
        let piv = 127 - v.leading_zeros();
        let pos = rows.iter().position(|&(rv, _)| (127 - rv.leading_zeros()) < piv).unwrap_or(rows.len());
        rows.insert(pos, (v, comb));
    }
    let mut gamma = vec![0u32; r]; // gamma[m] bit p*n+q
    for (pq, &e) in wbasis.iter().enumerate() {
        let mut v = e;
        let mut comb = 0u64;
        for &(rv, rc) in &rows {
            let piv = 127 - rv.leading_zeros();
            if v >> piv & 1 == 1 {
                v ^= rv;
                comb ^= rc;
            }
        }
        if v != 0 {
            return false;
        }
        for m in 0..r {
            if comb >> m & 1 == 1 {
                gamma[m] |= 1 << pq;
            }
        }
    }
    let factors: Vec<(u32, u32)> = basis.iter().map(|&b| g.factor(b)).collect();
    // Brent equations from scratch
    for a in 0..n {
        for b in 0..n {
            for c in 0..n {
                for d in 0..n {
                    for p in 0..n {
                        for q in 0..n {
                            let mut s = 0u32;
                            for m in 0..r {
                                let (al, be) = factors[m];
                                s ^= (al >> (a * n + b) & 1) & (be >> (c * n + d) & 1) & (gamma[m] >> (p * n + q) & 1);
                            }
                            let rhs = (b == c && a == p && d == q) as u32;
                            if s != rhs {
                                return false;
                            }
                        }
                    }
                }
            }
        }
    }
    true
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str, d: usize| -> usize {
        args.iter().position(|a| a == k).and_then(|i| args.get(i + 1)).and_then(|v| v.parse().ok()).unwrap_or(d)
    };
    let n = get("--n", 3);
    let r = get("--r", 11);
    let g = Geo { n, nn: n * n };
    let nn = g.nn;
    assert!(r >= nn, "rank below n^2 is refuted by dimension alone");
    let max_t = get("--max-t", r - nn).min(r - nn);
    let cap = get("--cap", 2_000_000_000) as u64;
    let threads = get("--threads", 10);
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().ok();

    let wbasis = g.target_basis();
    let wspan = {
        let mut s = Span::new();
        for &w in &wbasis {
            assert!(s.insert(w));
        }
        s
    };
    // all rank-one matrices
    let nz = (1u32 << nn) - 1;
    let all: Vec<M> = (1..=nz).flat_map(|a| (1..=nz).map(move |b| (a, b))).map(|(a, b)| g.outer(a, b)).collect();
    let t0 = Instant::now();
    let reps = orbit_reps(&g);
    println!(
        "n={n} N={nn} r={r}: {} rank-one matrices, {} orbits under GL_n(F_2)^3 ({:.2}s); dim W = {}; rank-one elements of W: {}",
        all.len(),
        reps.len(),
        t0.elapsed().as_secs_f64(),
        wspan.dim(),
        all.iter().filter(|&&v| wspan.reduce(v) == 0).count()
    );
    if r == nn {
        println!("rank {nn}: scheme exists iff W has a rank-one basis — {}", if all.iter().any(|&v| wspan.reduce(v) == 0) { "possible" } else { "UNSAT (no rank-one element in W)" });
    }

    let found = AtomicBool::new(false);
    let cubes = AtomicU64::new(0);
    let capped = AtomicBool::new(false);
    for t in 1..=max_t {
        if found.load(Ordering::Relaxed) || capped.load(Ordering::Relaxed) {
            break;
        }
        let t1 = Instant::now();
        let level_cubes = AtomicU64::new(0);
        // depth 1: orbit representatives (independent mod W: always, no rank-one in W)
        reps.par_iter().for_each(|&(a, b)| {
            if found.load(Ordering::Relaxed) || capped.load(Ordering::Relaxed) {
                return;
            }
            let v1 = g.outer(a, b);
            let mut base = wspan.clone();
            if !base.insert(v1) {
                return;
            }
            // recursive brute-force extenders v_2 < v_3 < ... (indices into `all`)
            fn rec(
                g: &Geo,
                wbasis: &[M],
                all: &[M],
                span: &Span,
                ext: &mut Vec<M>,
                start: usize,
                t: usize,
                cap: u64,
                cubes: &AtomicU64,
                level_cubes: &AtomicU64,
                found: &AtomicBool,
                capped: &AtomicBool,
            ) {
                if ext.len() == t {
                    let c = cubes.fetch_add(1, Ordering::Relaxed) + 1;
                    level_cubes.fetch_add(1, Ordering::Relaxed);
                    if c > cap {
                        capped.store(true, Ordering::Relaxed);
                        return;
                    }
                    if let Some(basis) = decide_cube(g, wbasis, ext) {
                        let ok = verify_scheme(g, wbasis, &basis);
                        println!(
                            "SAT-CANDIDATE: {} rank-one products span W (t={}) — Brent re-verification: {}",
                            basis.len(),
                            t,
                            if ok { "VALID SCHEME" } else { "INVALID (bug)" }
                        );
                        if ok {
                            found.store(true, Ordering::Relaxed);
                        }
                    }
                    return;
                }
                for i in start..all.len() {
                    if found.load(Ordering::Relaxed) || capped.load(Ordering::Relaxed) {
                        return;
                    }
                    let v = all[i];
                    if span.reduce(v) == 0 {
                        continue; // already in T
                    }
                    let mut s2 = span.clone();
                    s2.insert(v);
                    ext.push(v);
                    rec(g, wbasis, all, &s2, ext, i + 1, t, cap, cubes, level_cubes, found, capped);
                    ext.pop();
                }
            }
            let mut ext = vec![v1];
            rec(&g, &wbasis, &all, &base, &mut ext, 0, t, cap, &cubes, &level_cubes, &found, &capped);
        });
        println!(
            "t={t} (rank <= {}): {} cubes decided in {:.2}s{}{}",
            nn + t,
            level_cubes.load(Ordering::Relaxed),
            t1.elapsed().as_secs_f64(),
            if found.load(Ordering::Relaxed) { " — SAT" } else { " — no scheme" },
            if capped.load(Ordering::Relaxed) { " — CAP HIT (incomplete)" } else { "" }
        );
    }
    let verdict = if found.load(Ordering::Relaxed) {
        "SAT"
    } else if capped.load(Ordering::Relaxed) {
        "UNKNOWN (cap)"
    } else {
        "UNSAT"
    };
    println!(
        "VERDICT n={n} r={r} (t<={max_t}): {verdict}; {} cubes total, {:.2}s",
        cubes.load(Ordering::Relaxed),
        t0.elapsed().as_secs_f64()
    );
}
