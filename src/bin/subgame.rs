//! subgame — the automated substitution method over F_2: the
//! kill-one-product game on <n,n,n>.
//!
//! A rank-r decomposition sum_i a_i (x) b_i (x) c_i of a tensor T can be
//! cut by one product: quotient one side by that product's vector; the
//! image has rank <= r - 1. A minimal decomposition's vectors on a side
//! lie in that side's SUPPORT (the smallest S with T in S (x) ..) and span
//! it, so the prover may name any functional phi in U^perp that does not
//! vanish on S and the adversary must kill some v in S with phi . v = 1:
//!
//!   val(T) = max( flattening ranks of T,
//!                 max_{side, phi} ( 1 + min_{v in S, phi.v = 1} val(T / v) ) )
//!   (kill moves only for T != 0 — a zero tensor has no product)
//!
//! is a lower bound on R(T). States are the killed subspaces (U, V, X) as
//! RREF bases.
//!
//!   subgame --n 2 [--cert FILE]              exact game value (memoized)
//!   subgame --n 3 --ladder [--from K] [--cert FILE] [--nodes N] [--time S]
//!                                            decision procedure "val >= k",
//!                                            k = from, from+1, ... until it fails
//!   --coset                                  add the F_2 coset-counting leaf bound
//!   --stay                                   prover prefers the side with the most
//!                                            kills so far (one-sided strategies)
//!   --sym                                    memoize up to the GL_3(F_2)^3 sandwich
//!                                            symmetry (n = 3); certificates carry
//!                                            an explicit group element per child
//!
//! Certificates (the proof DAG: side + phi per prover node, all adversary
//! children, leaf facts) replay in matmul/r22/subgame_verify.py.
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::time::Instant;

type V = u16; // vector in F_2^d, d <= 9

/// reduced row echelon basis (unique per subspace), rows sorted descending
fn rref(rows: &[V]) -> Vec<V> {
    let mut out: Vec<V> = Vec::new();
    for &r in rows {
        let mut v = r;
        for &o in &out {
            let p = 15 - o.leading_zeros();
            if v >> p & 1 == 1 {
                v ^= o;
            }
        }
        if v != 0 {
            let p = 15 - v.leading_zeros();
            for o in out.iter_mut() {
                if *o >> p & 1 == 1 {
                    *o ^= v;
                }
            }
            out.push(v);
        }
    }
    out.sort_unstable_by(|a, b| b.cmp(a));
    out
}

/// annihilator basis of U in F_2^d plus the free columns f_i (e_i = 1 << f_i
/// is the dual basis: phi_j . e_i = [i = j])
fn annihilator_free(u: &[V], d: usize) -> (Vec<V>, Vec<usize>) {
    let r = rref(u);
    let pivots: Vec<usize> = r.iter().map(|&row| (15 - row.leading_zeros()) as usize).collect();
    let mut basis = Vec::new();
    let mut free = Vec::new();
    for f in 0..d {
        if pivots.contains(&f) {
            continue;
        }
        let mut phi: V = 1 << f;
        for (row, &p) in r.iter().zip(&pivots) {
            if row >> f & 1 == 1 {
                phi |= 1 << p;
            }
        }
        basis.push(phi);
        free.push(f);
    }
    (basis, free)
}

#[derive(Clone)]
struct Tensor {
    da: usize,
    db: usize,
    dc: usize,
    t: Vec<Vec<u32>>, // t[a][b] = bitmask over c
}

fn matmul_tensor(n: usize) -> Tensor {
    let d = n * n;
    let mut t = vec![vec![0u32; d]; d];
    for a in 0..n {
        for b in 0..n {
            for c in 0..n {
                for dd in 0..n {
                    for p in 0..n {
                        for q in 0..n {
                            if b == c && a == p && dd == q {
                                t[a * n + b][c * n + dd] |= 1 << (p * n + q);
                            }
                        }
                    }
                }
            }
        }
    }
    Tensor { da: d, db: d, dc: d, t }
}

fn parity(x: u32) -> u32 {
    x.count_ones() & 1
}
fn dot(a: V, b: V) -> u32 {
    (a & b).count_ones() & 1
}

/// T / (U, V, X): contract with the annihilator bases
fn quotient(t0: &Tensor, u: &[V], v: &[V], x: &[V]) -> Tensor {
    let (phi, _) = annihilator_free(u, t0.da);
    let (psi, _) = annihilator_free(v, t0.db);
    let (chi, _) = annihilator_free(x, t0.dc);
    let mut s1 = vec![vec![0u32; t0.db]; t0.da];
    for a in 0..t0.da {
        for b in 0..t0.db {
            let mut row = 0u32;
            for (k, &ck) in chi.iter().enumerate() {
                if parity(t0.t[a][b] & ck as u32) == 1 {
                    row |= 1 << k;
                }
            }
            s1[a][b] = row;
        }
    }
    let mut s2 = vec![vec![0u32; psi.len()]; t0.da];
    for a in 0..t0.da {
        for (j, &pj) in psi.iter().enumerate() {
            let mut row = 0u32;
            for b in 0..t0.db {
                if pj >> b & 1 == 1 {
                    row ^= s1[a][b];
                }
            }
            s2[a][j] = row;
        }
    }
    let mut t = vec![vec![0u32; psi.len()]; phi.len()];
    for (i, &fi) in phi.iter().enumerate() {
        for j in 0..psi.len() {
            let mut row = 0u32;
            for a in 0..t0.da {
                if fi >> a & 1 == 1 {
                    row ^= s2[a][j];
                }
            }
            t[i][j] = row;
        }
    }
    Tensor { da: phi.len(), db: psi.len(), dc: chi.len(), t }
}

fn rank_u128(rows: &mut Vec<u128>) -> usize {
    let mut rk = 0;
    let mut col = 127i32;
    while col >= 0 && rk < rows.len() {
        if let Some(p) = (rk..rows.len()).find(|&i| rows[i] >> col & 1 == 1) {
            rows.swap(rk, p);
            for i in 0..rows.len() {
                if i != rk && rows[i] >> col & 1 == 1 {
                    rows[i] ^= rows[rk];
                }
            }
            rk += 1;
        }
        col -= 1;
    }
    rk
}

/// slice vectors per side (A-slices as (b,c)-vectors, B-slices as (a,c), C-slices as (a,b))
fn slices(t: &Tensor, side: u8) -> Vec<u128> {
    match side {
        1 => (0..t.da)
            .map(|a| (0..t.db).fold(0u128, |acc, b| acc | ((t.t[a][b] as u128) << (b * t.dc))))
            .collect(),
        2 => (0..t.db)
            .map(|b| (0..t.da).fold(0u128, |acc, a| acc | ((t.t[a][b] as u128) << (a * t.dc))))
            .collect(),
        _ => (0..t.dc)
            .map(|c| {
                let mut v = 0u128;
                for a in 0..t.da {
                    for b in 0..t.db {
                        if t.t[a][b] >> c & 1 == 1 {
                            v |= 1u128 << (a * t.db + b);
                        }
                    }
                }
                v
            })
            .collect(),
    }
}

/// the three flattening ranks
fn flattenings(t: &Tensor) -> [usize; 3] {
    let mut f = [0usize; 3];
    for side in 1..=3u8 {
        let mut rows = slices(t, side);
        f[side as usize - 1] = rank_u128(&mut rows);
    }
    f
}

/// rank of a matrix given as a bit-vector with `cols` columns per row
fn matrix_rank(v: u128, rows: usize, cols: usize) -> usize {
    let mask = (1u128 << cols) - 1;
    let mut rs: Vec<u128> = (0..rows).map(|r| (v >> (r * cols)) & mask).collect();
    rank_u128(&mut rs)
}

/// F_2 coset-counting leaf bound, per side. If every nonzero element of a
/// side's slice span (dim w) has rank >= 3, distinct rank-one products
/// inject into the nonzero cosets of the span inside their own span, so
/// r <= 2^(r - w) - 1; returns the least r satisfying it (0 if the premise
/// fails on every side).
fn coset_bound(t: &Tensor) -> usize {
    let mut best = 0;
    for side in 1..=3u8 {
        let (rows_n, cols_n) = match side {
            1 => (t.db, t.dc),
            2 => (t.da, t.dc),
            _ => (t.da, t.db),
        };
        let mut basis = slices(t, side);
        let w = rank_u128(&mut basis);
        if w == 0 {
            continue;
        }
        let basis: Vec<u128> = basis.into_iter().filter(|&r| r != 0).collect();
        let mut ok = true;
        for code in 1u32..(1u32 << w) {
            let mut m = 0u128;
            for (i, &b) in basis.iter().enumerate() {
                if code >> i & 1 == 1 {
                    m ^= b;
                }
            }
            if matrix_rank(m, rows_n, cols_n) <= 2 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let mut r = w;
        while !(r <= (1usize << (r - w)) - 1) {
            r += 1;
        }
        best = best.max(r);
    }
    best
}

/// support of the quotient tensor on one side, as a subspace of the
/// ORIGINAL space containing the killed subspace
fn support(t: &Tensor, side: u8, killed: &[V], d: usize) -> Vec<V> {
    let (_, free) = annihilator_free(killed, d);
    let cols: Vec<u32> = match side {
        1 => {
            let mut c = Vec::new();
            for b in 0..t.db {
                for k in 0..t.dc {
                    let mut y = 0u32;
                    for i in 0..t.da {
                        if t.t[i][b] >> k & 1 == 1 {
                            y |= 1 << i;
                        }
                    }
                    c.push(y);
                }
            }
            c
        }
        2 => {
            let mut c = Vec::new();
            for i in 0..t.da {
                for k in 0..t.dc {
                    let mut y = 0u32;
                    for j in 0..t.db {
                        if t.t[i][j] >> k & 1 == 1 {
                            y |= 1 << j;
                        }
                    }
                    c.push(y);
                }
            }
            c
        }
        _ => {
            let mut c = Vec::new();
            for i in 0..t.da {
                for j in 0..t.db {
                    c.push(t.t[i][j]);
                }
            }
            c
        }
    };
    let mut rows: Vec<V> = killed.to_vec();
    for y in cols {
        let mut v: V = 0;
        for (i, &f) in free.iter().enumerate() {
            if y >> i & 1 == 1 {
                v |= 1 << f;
            }
        }
        rows.push(v);
    }
    rref(&rows)
}

fn elements(basis: &[V]) -> Vec<V> {
    let mut out = Vec::with_capacity(1 << basis.len());
    for code in 0..(1u32 << basis.len()) {
        let mut v: V = 0;
        for (i, &b) in basis.iter().enumerate() {
            if code >> i & 1 == 1 {
                v ^= b;
            }
        }
        out.push(v);
    }
    out
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct State {
    u: Vec<V>,
    v: Vec<V>,
    x: Vec<V>,
}

impl State {
    fn side(&self, s: u8) -> &Vec<V> {
        match s {
            1 => &self.u,
            2 => &self.v,
            _ => &self.x,
        }
    }
    fn with(&self, s: u8, e: Vec<V>) -> State {
        match s {
            1 => State { u: e, v: self.v.clone(), x: self.x.clone() },
            2 => State { u: self.u.clone(), v: e, x: self.x.clone() },
            _ => State { u: self.u.clone(), v: self.v.clone(), x: e },
        }
    }
}

/// the adversary's options for (side, phi): U + <v>, v in supp, phi.v = 1
fn forced_extensions(supp_el: &[V], cur: &[V], phi: V) -> Vec<Vec<V>> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for &v in supp_el {
        if dot(phi, v) != 1 {
            continue;
        }
        let mut rows = cur.to_vec();
        rows.push(v);
        let e = rref(&rows);
        if e.len() == cur.len() || !seen.insert(e.clone()) {
            continue;
        }
        out.push(e);
    }
    out
}

// ---------------- symmetry: the sandwich group GL_3(F_2)^3 ----------------
// g = (P, Q, R) acts on the three matrix spaces (9-bit row-major 3x3 bit matrices):
//   A: alpha -> P^T alpha Q^T,  B: beta -> Q^-T beta R^T,  C: gamma -> P^-1 gamma R^-1
// which preserves the <3,3,3> tensor (checked at startup). Only for n = 3.
fn m3_mul(a: u16, b: u16) -> u16 {
    let mut c = 0u16;
    for i in 0..3 {
        for j in 0..3 {
            let mut s = 0;
            for k in 0..3 {
                s ^= (a >> (i * 3 + k) & 1) & (b >> (k * 3 + j) & 1);
            }
            c |= s << (i * 3 + j);
        }
    }
    c
}
fn m3_tr(a: u16) -> u16 {
    let mut c = 0u16;
    for i in 0..3 {
        for j in 0..3 {
            c |= (a >> (i * 3 + j) & 1) << (j * 3 + i);
        }
    }
    c
}

struct Sym {
    gl: Vec<u16>,            // the 168 invertible matrices
    idx: Vec<u16>,           // matrix -> index (u16::MAX if singular)
    inv: Vec<usize>,         // index -> index of inverse
    tr: Vec<usize>,          // index -> index of transpose
    // act[(p * 168 + q) * 512 + m] = gl[p] * m * gl[q]
    act: Vec<u16>,
}

impl Sym {
    fn new() -> Sym {
        let id: u16 = 0b100_010_001;
        let mut gl = Vec::new();
        for m in 0..512u16 {
            // invertible iff some b with m*b = id; brute force
            if (0..512u16).any(|b| m3_mul(m, b) == id) {
                gl.push(m);
            }
        }
        assert_eq!(gl.len(), 168);
        let mut idx = vec![u16::MAX; 512];
        for (i, &m) in gl.iter().enumerate() {
            idx[m as usize] = i as u16;
        }
        let inv: Vec<usize> = gl.iter().map(|&m| gl.iter().position(|&b| m3_mul(m, b) == id).unwrap()).collect();
        let tr: Vec<usize> = gl.iter().map(|&m| idx[m3_tr(m) as usize] as usize).collect();
        let mut act = vec![0u16; 168 * 168 * 512];
        for p in 0..168 {
            for q in 0..168 {
                for m in 0..512u16 {
                    act[(p * 168 + q) * 512 + m as usize] = m3_mul(m3_mul(gl[p], m), gl[q]);
                }
            }
        }
        Sym { gl, idx, inv, tr, act }
    }
    #[inline]
    fn ap(&self, p: usize, q: usize, m: V) -> V {
        self.act[(p * 168 + q) * 512 + m as usize]
    }
    /// transform a subspace basis and re-echelonize
    fn sub(&self, p: usize, q: usize, rows: &[V]) -> Vec<V> {
        let v: Vec<V> = rows.iter().map(|&m| self.ap(p, q, m)).collect();
        rref(&v)
    }
    /// the three side actions for g = (P, Q, R) given as indices
    fn act_a(&self, g: (usize, usize, usize), rows: &[V]) -> Vec<V> {
        self.sub(self.tr[g.0], self.tr[g.1], rows)
    }
    fn act_b(&self, g: (usize, usize, usize), rows: &[V]) -> Vec<V> {
        self.sub(self.tr[self.inv[g.1]], self.tr[g.2], rows)
    }
    fn act_c(&self, g: (usize, usize, usize), rows: &[V]) -> Vec<V> {
        self.sub(self.inv[g.0], self.inv[g.2], rows)
    }
    fn apply(&self, g: (usize, usize, usize), s: &State) -> State {
        State { u: self.act_a(g, &s.u), v: self.act_b(g, &s.v), x: self.act_c(g, &s.x) }
    }
    /// lexicographically least image of the state under the group, with a
    /// group element realizing it. Staged: U over all (P,Q); V over the
    /// minimizers with R free; X over the remaining minimizers.
    fn canon(&self, s: &State) -> (State, (usize, usize, usize)) {
        let (c, g, _) = self.canon_full(s);
        (c, g)
    }
    /// as canon(), plus ALL group elements realizing the canonical image
    /// (r = usize::MAX means "any R"). For a canonical state this set is its
    /// stabilizer.
    fn canon_full(&self, s: &State) -> (State, (usize, usize, usize), Vec<(usize, usize, usize)>) {
        // stage 1: U
        let mut best_u: Option<Vec<V>> = None;
        let mut s1: Vec<(usize, usize)> = Vec::new();
        if s.u.is_empty() {
            for p in 0..168 {
                for q in 0..168 {
                    s1.push((p, q));
                }
            }
            best_u = Some(vec![]);
        } else {
            for p in 0..168 {
                for q in 0..168 {
                    let img = self.sub(self.tr[p], self.tr[q], &s.u);
                    match &best_u {
                        Some(b) if img > *b => {}
                        Some(b) if img == *b => s1.push((p, q)),
                        _ => {
                            best_u = Some(img);
                            s1.clear();
                            s1.push((p, q));
                        }
                    }
                }
            }
        }
        // stage 2: V with R free
        let mut best_v: Option<Vec<V>> = None;
        let mut s2: Vec<(usize, usize, usize)> = Vec::new();
        if s.v.is_empty() {
            best_v = Some(vec![]);
            // keep (P,Q) and leave R open: represent by r = usize::MAX
            for &(p, q) in &s1 {
                s2.push((p, q, usize::MAX));
            }
        } else {
            for &(p, q) in &s1 {
                let qi = self.tr[self.inv[q]];
                for r in 0..168 {
                    let img = self.sub(qi, self.tr[r], &s.v);
                    match &best_v {
                        Some(b) if img > *b => {}
                        Some(b) if img == *b => s2.push((p, q, r)),
                        _ => {
                            best_v = Some(img);
                            s2.clear();
                            s2.push((p, q, r));
                        }
                    }
                }
            }
        }
        // stage 3: X
        let mut best_x: Option<Vec<V>> = None;
        let mut best_g = (0usize, 0usize, 0usize);
        let mut s3: Vec<(usize, usize, usize)> = Vec::new();
        if s.x.is_empty() {
            let (p, q, r) = s2[0];
            best_g = (p, q, if r == usize::MAX { 0 } else { r });
            best_x = Some(vec![]);
            s3 = s2;
        } else {
            for &(p, q, r) in &s2 {
                let rs: Vec<usize> = if r == usize::MAX { (0..168).collect() } else { vec![r] };
                for r in rs {
                    let img = self.sub(self.inv[p], self.inv[r], &s.x);
                    match &best_x {
                        Some(b) if img > *b => {}
                        Some(b) if img == *b => s3.push((p, q, r)),
                        _ => {
                            best_x = Some(img);
                            best_g = (p, q, r);
                            s3.clear();
                            s3.push((p, q, r));
                        }
                    }
                }
            }
        }
        let c = State { u: best_u.unwrap(), v: best_v.unwrap(), x: best_x.unwrap() };
        (c, best_g, s3)
    }

    /// dual action of g on a functional of the given side:
    ///   A: phi -> P phi Q,  B: psi -> Q^-1 psi R,  C: chi -> P^-T chi R^-T
    fn dual(&self, g: (usize, usize, usize), side: u8, phi: V) -> V {
        match side {
            1 => self.ap(g.0, g.1, phi),
            2 => self.ap(self.inv[g.1], g.2, phi),
            _ => self.ap(self.tr[self.inv[g.0]], self.tr[self.inv[g.2]], phi),
        }
    }

    /// reduce a list of prover functionals to orbit representatives under
    /// a stabilizer (r = MAX entries expand over all R; skipped if too big)
    fn phi_reps(&self, stab: &[(usize, usize, usize)], side: u8, phis: &[V], is_root: bool) -> Vec<V> {
        if is_root {
            // full group: orbits of nonzero 3x3 matrices are the rank classes
            let mut reps: Vec<V> = Vec::new();
            let mut seen_rank = [false; 4];
            for &p in phis {
                let rk = matrix_rank(p as u128, 3, 3);
                if !seen_rank[rk] {
                    seen_rank[rk] = true;
                    reps.push(p);
                }
            }
            return reps;
        }
        let expanded: usize = stab.iter().map(|&(_, _, r)| if r == usize::MAX { 168 } else { 1 }).sum();
        if expanded > 200_000 {
            return phis.to_vec();
        }
        let mut elems: Vec<(usize, usize, usize)> = Vec::with_capacity(expanded);
        for &(p, q, r) in stab {
            if r == usize::MAX {
                for rr in 0..168 {
                    elems.push((p, q, rr));
                }
            } else {
                elems.push((p, q, r));
            }
        }
        let mut seen: HashSet<V> = HashSet::new();
        let mut reps = Vec::new();
        for &phi in phis {
            let mut m = phi;
            for &g in &elems {
                let img = self.dual(g, side, phi);
                if img < m {
                    m = img;
                }
            }
            if seen.insert(m) {
                reps.push(phi);
            }
        }
        reps
    }
}

/// gate: the sandwich action preserves the <3,3,3> tensor
fn check_symmetry(sym: &Sym, t0: &Tensor) {
    let d = 9;
    for &g in &[(1usize, 2usize, 3usize), (17, 5, 100), (160, 77, 9), (3, 3, 3)] {
        // transform T0: (g.T)[a'][b'][c'] = sum T[a][b][c] [gA e_a]_a' [gB e_b]_b' [gC e_c]_c'
        let ga = |m: V| sym.ap(sym.tr[g.0], sym.tr[g.1], m);
        let gb = |m: V| sym.ap(sym.tr[sym.inv[g.1]], sym.tr[g.2], m);
        let gc = |m: V| sym.ap(sym.inv[g.0], sym.inv[g.2], m);
        let mut tt = vec![vec![0u32; d]; d];
        for a in 0..d {
            let ia = ga(1 << a);
            for b in 0..d {
                let ib = gb(1 << b);
                for c in 0..d {
                    if t0.t[a][b] >> c & 1 == 0 {
                        continue;
                    }
                    let ic = gc(1 << c);
                    for a2 in 0..d {
                        if ia >> a2 & 1 == 0 {
                            continue;
                        }
                        for b2 in 0..d {
                            if ib >> b2 & 1 == 0 {
                                continue;
                            }
                            tt[a2][b2] ^= ic as u32;
                        }
                    }
                }
            }
        }
        assert!(tt == t0.t, "sandwich action does not preserve the tensor for g = {g:?}");
    }
}

#[derive(Clone)]
struct Proof {
    value: u32, // proven lower bound
    choice: u8, // 0 = leaf, 1/2/3 = kill on A/B/C
    phi: V,
    leaf: [usize; 3],
    dims: (usize, usize, usize),
}

struct Game {
    t0: Tensor,
    d: usize,
    rank_ub: u32,
    coset: bool,
    stay: bool,
    sym: Option<Sym>,
    stab_cache: HashMap<State, Vec<(usize, usize, usize)>>,
    canon_cache: HashMap<State, (State, (usize, usize, usize))>,
    isos: HashMap<State, (State, (usize, usize, usize))>, // raw child -> (canonical, g) for the certificate
    memo: HashMap<State, Proof>,
    lo: HashMap<State, u32>,
    hi: HashMap<State, u32>,
    proofs: HashMap<State, Proof>,
    nodes: u64,
    node_cap: u64,
    t_start: Instant,
    time_cap: f64,
    capped: bool,
}

impl Game {
    // ---------------- exact game (small n) ----------------
    fn val(&mut self, s: &State) -> u32 {
        if let Some(n) = self.memo.get(s) {
            return n.value;
        }
        let t = quotient(&self.t0, &s.u, &s.v, &s.x);
        let leaf = flattenings(&t);
        let mut best = *leaf.iter().max().unwrap() as u32;
        if self.coset {
            best = best.max(coset_bound(&t) as u32);
        }
        let mut choice = 0u8;
        let mut best_phi: V = 0;
        let dims = (t.da, t.db, t.dc);
        let nonzero = leaf.iter().any(|&f| f > 0);
        for side in 1..=3u8 {
            if !nonzero {
                break;
            }
            let cur = s.side(side);
            if cur.len() >= self.d {
                continue;
            }
            let supp = support(&t, side, cur, self.d);
            let supp_el = elements(&supp);
            let (ann, _) = annihilator_free(cur, self.d);
            for phi in elements(&ann).into_iter().filter(|&p| p != 0) {
                if !supp.iter().any(|&sv| dot(phi, sv) == 1) {
                    continue;
                }
                let mut worst = u32::MAX;
                for e in forced_extensions(&supp_el, cur, phi) {
                    let cv = self.val(&s.with(side, e));
                    worst = worst.min(cv);
                    if 1 + worst <= best {
                        break;
                    }
                }
                if worst != u32::MAX && 1 + worst > best {
                    best = 1 + worst;
                    choice = side;
                    best_phi = phi;
                }
            }
        }
        self.memo.insert(s.clone(), Proof { value: best, choice, phi: best_phi, leaf, dims });
        best
    }

    /// canonical representative of a state (identity when symmetry is off)
    fn canon(&mut self, s: &State) -> State {
        let Some(sym) = &self.sym else { return s.clone() };
        if let Some((c, _)) = self.canon_cache.get(s) {
            return c.clone();
        }
        let (c, g) = sym.canon(s);
        self.canon_cache.insert(s.clone(), (c.clone(), g));
        self.isos.insert(s.clone(), (c.clone(), g));
        c
    }

    /// stabilizer of a canonical state (its own minimizer set), cached
    fn stabilizer(&mut self, c: &State) -> Vec<(usize, usize, usize)> {
        if let Some(st) = self.stab_cache.get(c) {
            return st.clone();
        }
        let st = match &self.sym {
            Some(sym) => sym.canon_full(c).2,
            None => vec![],
        };
        self.stab_cache.insert(c.clone(), st.clone());
        st
    }

    // ---------------- decision procedure: val(s) >= k ? ----------------
    fn record(&mut self, s: &State, p: Proof) {
        let cur = self.proofs.get(s).map(|q| q.value).unwrap_or(0);
        if p.value > cur {
            self.proofs.insert(s.clone(), p);
        }
    }

    fn prove(&mut self, s: &State, k: u32) -> bool {
        if k == 0 {
            return true;
        }
        let lo = *self.lo.get(s).unwrap_or(&0);
        if k <= lo {
            return true;
        }
        let hi = *self.hi.get(s).unwrap_or(&u32::MAX);
        if k >= hi {
            return false;
        }
        self.nodes += 1;
        if self.nodes > self.node_cap || self.t_start.elapsed().as_secs_f64() > self.time_cap {
            self.capped = true;
            return false;
        }
        let t = quotient(&self.t0, &s.u, &s.v, &s.x);
        let leaf = flattenings(&t);
        let dims = (t.da, t.db, t.dc);
        let mut lb = *leaf.iter().max().unwrap() as u32;
        if self.coset {
            lb = lb.max(coset_bound(&t) as u32);
        }
        if lb > lo {
            self.lo.insert(s.clone(), lb);
            self.record(s, Proof { value: lb, choice: 0, phi: 0, leaf, dims });
        }
        if lb >= k {
            return true;
        }
        if lb == 0 {
            self.hi.insert(s.clone(), 1);
            return false;
        }
        let ub = (dims.0 * dims.1).min(dims.0 * dims.2).min(dims.1 * dims.2) as u32;
        let ub = ub.min(self.rank_ub);
        if k > ub {
            self.hi.insert(s.clone(), hi.min(ub + 1));
            return false;
        }
        // prover: sides ordered by free support dimension (largest first), phi by weight
        let mut sides: Vec<(usize, u8, Vec<V>, Vec<V>)> = Vec::new();
        for side in 1..=3u8 {
            let cur = s.side(side);
            if cur.len() >= self.d {
                continue;
            }
            let supp = support(&t, side, cur, self.d);
            let free_dim = supp.len() - cur.len();
            if free_dim == 0 {
                continue;
            }
            sides.push((free_dim, side, supp, cur.clone()));
        }
        if self.stay {
            // prefer the side with the most kills so far (one-sided strategies
            // keep the state space to subspaces of ONE side); ties -> A, B, C
            sides.sort_by(|a, b| s.side(b.1).len().cmp(&s.side(a.1).len()).then(a.1.cmp(&b.1)));
        } else {
            sides.sort_by(|a, b| b.0.cmp(&a.0));
        }
        let is_root = s.u.is_empty() && s.v.is_empty() && s.x.is_empty();
        let stab = if self.sym.is_some() { self.stabilizer(s) } else { vec![] };
        for (_, side, supp, cur) in sides {
            let supp_el = elements(&supp);
            let (ann, _) = annihilator_free(&cur, self.d);
            let mut phis: Vec<V> = elements(&ann).into_iter().filter(|&p| p != 0).collect();
            phis.retain(|&p| supp.iter().any(|&sv| dot(p, sv) == 1));
            phis.sort_by_key(|p| p.count_ones());
            if let Some(sym) = &self.sym {
                phis = sym.phi_reps(&stab, side, &phis, is_root);
            }
            for phi in phis {
                let exts = forced_extensions(&supp_el, &cur, phi);
                // adversary: hardest children first (smallest quick lower bound)
                let mut kids: Vec<(u32, State)> = exts
                    .into_iter()
                    .map(|e| {
                        let raw = s.with(side, e);
                        let c = self.canon(&raw);
                        let known = *self.lo.get(&c).unwrap_or(&0);
                        let q = if known >= k - 1 {
                            known
                        } else {
                            let tc = quotient(&self.t0, &c.u, &c.v, &c.x);
                            *flattenings(&tc).iter().max().unwrap() as u32
                        };
                        (q, c)
                    })
                    .collect();
                kids.sort_by_key(|(q, _)| *q);
                kids.dedup_by(|a, b| a.1 == b.1);
                let mut all_ok = true;
                for (_, c) in &kids {
                    if !self.prove(c, k - 1) {
                        all_ok = false;
                        break;
                    }
                }
                if self.capped {
                    return false;
                }
                if all_ok {
                    self.lo.insert(s.clone(), k);
                    self.record(s, Proof { value: k, choice: side, phi, leaf, dims });
                    return true;
                }
            }
        }
        self.hi.insert(s.clone(), k);
        false
    }
}

fn key(s: &State) -> String {
    let f = |v: &[V]| v.iter().map(|x| format!("{x:x}")).collect::<Vec<_>>().join(",");
    format!("{}|{}|{}", f(&s.u), f(&s.v), f(&s.x))
}

/// certificate DAG from the proof records: chosen side/phi at prover nodes,
/// ALL forced children at adversary nodes, leaf facts
fn certificate(g: &Game, n: usize, root: &State, proofs: &HashMap<State, Proof>) -> String {
    let mut out = String::new();
    let mut seen = HashSet::new();
    let mut stack = vec![root.clone()];
    let mut lines = Vec::new();
    while let Some(s) = stack.pop() {
        if !seen.insert(key(&s)) {
            continue;
        }
        let node = proofs.get(&s).expect("proof record missing");
        let mut line = String::new();
        write!(
            line,
            "{{\"key\":\"{}\",\"dims\":[{},{},{}],\"value\":{},\"choice\":{},\"phi\":{},\"leaf\":[{},{},{}]",
            key(&s), node.dims.0, node.dims.1, node.dims.2, node.value, node.choice, node.phi, node.leaf[0], node.leaf[1], node.leaf[2]
        )
        .unwrap();
        if node.choice != 0 {
            let cur = s.side(node.choice);
            let t = quotient(&g.t0, &s.u, &s.v, &s.x);
            let supp = support(&t, node.choice, cur, g.d);
            let mut ks = Vec::new();
            for e in forced_extensions(&elements(&supp), cur, node.phi) {
                let child = s.with(node.choice, e);
                match g.isos.get(&child) {
                    Some((c, gg)) if g.sym.is_some() => {
                        let sym = g.sym.as_ref().unwrap();
                        ks.push(format!(
                            "{{\"raw\":\"{}\",\"canon\":\"{}\",\"g\":[{},{},{}]}}",
                            key(&child), key(c), sym.gl[gg.0], sym.gl[gg.1], sym.gl[gg.2]
                        ));
                        stack.push(c.clone());
                    }
                    _ => {
                        ks.push(format!("{{\"raw\":\"{}\"}}", key(&child)));
                        stack.push(child);
                    }
                }
            }
            write!(line, ",\"children\":[{}]", ks.join(",")).unwrap();
        }
        line.push('}');
        lines.push(line);
    }
    writeln!(out, "{{\"n\":{n},\"coset\":{},\"root\":\"{}\",\"nodes\":[", g.coset, key(root)).unwrap();
    out.push_str(&lines.join(",\n"));
    out.push_str("\n]}\n");
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned());
    let flag = |k: &str| args.iter().any(|a| a == k);
    let n: usize = get("--n").and_then(|v| v.parse().ok()).unwrap_or(2);
    let cert = get("--cert");
    let coset = flag("--coset");
    let rank_ub: u32 = get("--rank-ub").and_then(|v| v.parse().ok()).unwrap_or(if n == 2 { 7 } else { 23 });
    let t0 = matmul_tensor(n);
    let d = n * n;
    let sym = if flag("--sym") {
        assert_eq!(n, 3, "--sym implements the 3x3 sandwich group");
        let ts = Instant::now();
        let sy = Sym::new();
        check_symmetry(&sy, &t0);
        eprintln!("symmetry tables built ({:.1}s); sandwich action verified on the tensor", ts.elapsed().as_secs_f64());
        Some(sy)
    } else {
        None
    };
    let mut g = Game {
        t0,
        d,
        rank_ub,
        coset,
        stay: flag("--stay"),
        sym,
        stab_cache: HashMap::new(),
        canon_cache: HashMap::new(),
        isos: HashMap::new(),
        memo: HashMap::new(),
        lo: HashMap::new(),
        hi: HashMap::new(),
        proofs: HashMap::new(),
        nodes: 0,
        node_cap: get("--nodes").and_then(|v| v.parse().ok()).unwrap_or(50_000_000),
        t_start: Instant::now(),
        time_cap: get("--time").and_then(|v| v.parse().ok()).unwrap_or(600.0),
        capped: false,
    };
    let root = State { u: vec![], v: vec![], x: vec![] };
    if flag("--ladder") {
        let from: u32 = get("--from").and_then(|v| v.parse().ok()).unwrap_or(1);
        let mut proven = 0u32;
        let mut k = from;
        loop {
            let t = Instant::now();
            let ok = g.prove(&root, k);
            if g.capped {
                println!(
                    "k={k}: CAP (nodes {} / {:.1}s) — last proven {proven}",
                    g.nodes,
                    g.t_start.elapsed().as_secs_f64()
                );
                break;
            }
            if ok {
                proven = k;
                println!(
                    "k={k}: PROVED val >= {k}  (+{:.2}s, {} nodes total, {} states)",
                    t.elapsed().as_secs_f64(),
                    g.nodes,
                    g.lo.len()
                );
                k += 1;
            } else {
                println!(
                    "k={k}: FAILS — exact game value = {proven}  ({} nodes, {:.2}s)",
                    g.nodes,
                    g.t_start.elapsed().as_secs_f64()
                );
                break;
            }
        }
        println!(
            "=> rank_F2(<{n},{n},{n}>) >= {proven} by the substitution game{}",
            if coset { " + coset bound" } else { "" }
        );
        if let Some(path) = cert {
            if proven > 0 {
                if g.proofs.len() > 300_000 {
                    println!("certificate skipped: {} proof records (too large to write)", g.proofs.len());
                } else {
                    let c = certificate(&g, n, &root, &g.proofs);
                    std::fs::write(&path, &c).expect("write cert");
                    println!("certificate: {} ({} bytes)", path, c.len());
                }
            }
        }
    } else {
        let t = Instant::now();
        let value = g.val(&root);
        let node = g.memo[&root].clone();
        println!(
            "subgame <{n},{n},{n}> over F_2: game value = {value} (root choice: {}, root flattenings {:?}); {} states memoized in {:.2}s",
            ["leaf", "kill on A", "kill on B", "kill on C"][node.choice as usize],
            node.leaf,
            g.memo.len(),
            t.elapsed().as_secs_f64()
        );
        println!(
            "=> rank_F2(<{n},{n},{n}>) >= {value} by the substitution game{}",
            if coset { " + coset bound" } else { "" }
        );
        if let Some(path) = cert {
            let c = certificate(&g, n, &root, &g.memo);
            std::fs::write(&path, &c).expect("write cert");
            println!("certificate: {} ({} bytes)", path, c.len());
        }
    }
}
