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
//!   subgame --n 3 --ladder [--from K] [--to K] [--cert FILE] [--nodes N] [--time S]
//!                                            decision procedure "val >= k",
//!                                            k = from, from+1, ... until it fails
//!   --coset                                  add the F_2 coset-counting leaf bound
//!   --koszul P                               add Koszul-flattening leaves (p <= P)
//!   --root-bounds                            print the root's leaf bounds and exit
//!   --stay                                   prover prefers the side with the most
//!                                            kills so far (one-sided strategies)
//!   --sides AB | --onesided (= A)            restrict the prover's sides (still a
//!                                            lower bound); the root kill is on the
//!                                            first listed side (WLOG by the S_3
//!                                            tensor symmetry)
//!   --cert-max N                             skip the certificate above N proof records
//!   --heartbeat S                            progress line on stderr every S seconds
//!   --par D                                  evaluate adversary branches in parallel
//!                                            while the state has <= D kills
//!   --sym                                    memoize up to the GL_3(F_2)^3 sandwich
//!                                            symmetry (n = 3); certificates carry
//!                                            an explicit group element per child
//!
//! Certificates (the proof DAG: side + phi per prover node, all adversary
//! children, leaf facts) replay in matmul/r22/subgame_verify.py.
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Mutex;
use std::time::Instant;

use rayon::prelude::*;

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

/// rank over F_2 of a wide 0/1 matrix given as rows of u64 bitsets
fn rank_wide(rows: &mut Vec<Vec<u64>>, words: usize) -> usize {
    let mut rk = 0;
    let nrows = rows.len();
    for w in (0..words).rev() {
        for bit in (0..64).rev() {
            if rk >= nrows {
                return rk;
            }
            let piv = (rk..nrows).find(|&i| rows[i][w] >> bit & 1 == 1);
            let Some(piv) = piv else { continue };
            rows.swap(rk, piv);
            let (head, tail) = rows.split_at_mut(rk + 1);
            let prow = &head[rk];
            for r in tail.iter_mut() {
                if r[w] >> bit & 1 == 1 {
                    for x in 0..words {
                        r[x] ^= prow[x];
                    }
                }
            }
            rk += 1;
        }
    }
    rk
}

fn binom(n: usize, k: usize) -> usize {
    if k > n {
        return 0;
    }
    let mut r = 1usize;
    for i in 0..k {
        r = r * (n - i) / (i + 1);
    }
    r
}

/// Koszul flattening bound on side A with parameter p (1 <= p <= da-2):
/// rank(T^{wedge p}) / C(da-1, p), rounded up. Rows (S' in Λ^{p+1}, k in C),
/// columns (S in Λ^p, j in B); entry T[i][j][k] at (S u {i}, k), (S, j) for
/// i not in S (signs vanish over F_2). Valid over any field.
fn koszul_side(t: &Tensor, p: usize) -> usize {
    let (da, db, dc) = (t.da, t.db, t.dc);
    if da < 3 || p == 0 || p + 2 > da {
        return 0;
    }
    let mut idx_p: HashMap<u32, usize> = HashMap::new();
    let mut idx_q: HashMap<u32, usize> = HashMap::new();
    for m in 0..(1u32 << da) {
        let c = m.count_ones() as usize;
        if c == p {
            let n = idx_p.len();
            idx_p.insert(m, n);
        } else if c == p + 1 {
            let n = idx_q.len();
            idx_q.insert(m, n);
        }
    }
    let ncols = idx_p.len() * db;
    let nrows = idx_q.len() * dc;
    let words = (ncols + 63) / 64;
    let mut rows = vec![vec![0u64; words]; nrows];
    for (&sm, &si) in &idx_p {
        for i in 0..da {
            if sm >> i & 1 == 1 {
                continue;
            }
            let qi = idx_q[&(sm | (1 << i))];
            for j in 0..db {
                let col = si * db + j;
                let bits = t.t[i][j];
                if bits == 0 {
                    continue;
                }
                for k in 0..dc {
                    if bits >> k & 1 == 1 {
                        rows[qi * dc + k][col / 64] |= 1u64 << (col % 64);
                    }
                }
            }
        }
    }
    let rk = rank_wide(&mut rows, words);
    let denom = binom(da - 1, p);
    (rk + denom - 1) / denom
}

/// the tensor with the roles of the sides permuted so that `side` becomes A
fn with_side_first(t: &Tensor, side: u8) -> Tensor {
    match side {
        1 => t.clone(),
        2 => {
            let mut nt = vec![vec![0u32; t.da]; t.db];
            for i in 0..t.da {
                for j in 0..t.db {
                    nt[j][i] = t.t[i][j];
                }
            }
            Tensor { da: t.db, db: t.da, dc: t.dc, t: nt }
        }
        _ => {
            let mut nt = vec![vec![0u32; t.da]; t.dc];
            for i in 0..t.da {
                for j in 0..t.db {
                    for k in 0..t.dc {
                        if t.t[i][j] >> k & 1 == 1 {
                            nt[k][i] |= 1 << j;
                        }
                    }
                }
            }
            Tensor { da: t.dc, db: t.da, dc: t.db, t: nt }
        }
    }
}

/// max Koszul bound over the three sides and all p <= pmax (0 = none)
fn koszul_bound(t: &Tensor, pmax: usize) -> usize {
    let mut best = 0;
    for side in 1..=3u8 {
        let ts = with_side_first(t, side);
        if ts.da < 3 {
            continue;
        }
        for p in 1..=(ts.da - 2).min(pmax) {
            best = best.max(koszul_side(&ts, p));
        }
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

/// per-side minimum-rank constraints on ALIVE products' original-space
/// vectors (1 = trivial). Sound semantics: a product alive at (U,V,X)
/// (contributing nonzero to the quotient) has side-s vector of rank >= r_s.
/// Aliveness only shrinks as kills accumulate, so constraints persist.
type Rmin = [u8; 3];

#[derive(Clone, PartialEq, Eq, Hash)]
struct GState {
    s: State,
    rmin: Rmin,
}

/// rank of a 3x3 bit matrix (9-bit row-major)
fn rank3(m: V) -> u8 {
    let mut rows = [(m & 7) as u16, (m >> 3 & 7) as u16, (m >> 6 & 7) as u16];
    let mut rk = 0u8;
    for c in (0..3).rev() {
        if let Some(pi) = (rk as usize..3).find(|&i| rows[i] >> c & 1 == 1) {
            rows.swap(rk as usize, pi);
            for i in 0..3 {
                if i != rk as usize && rows[i] >> c & 1 == 1 {
                    rows[i] ^= rows[rk as usize];
                }
            }
            rk += 1;
        }
    }
    rk
}

/// does the coset (ext \ cur) contain a representative with rank in [lo, hi]?
/// (enumerates span(ext), skipping span(cur))
fn coset_has_rank(ext: &[V], cur: &[V], lo: u8, hi: u8) -> bool {
    let cur_r = rref(cur);
    let in_cur = |mut v: V| {
        for &o in &cur_r {
            let p = 15 - o.leading_zeros();
            if v >> p & 1 == 1 {
                v ^= o;
            }
        }
        v == 0
    };
    for code in 1u32..(1u32 << ext.len()) {
        let mut v: V = 0;
        for (i, &b) in ext.iter().enumerate() {
            if code >> i & 1 == 1 {
                v ^= b;
            }
        }
        if v == 0 || in_cur(v) {
            continue;
        }
        let r = rank3(v);
        if r >= lo && r <= hi {
            return true;
        }
    }
    false
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

/// every coset extension U + <v>, v in supp (no functional filter)
fn all_extensions(supp_el: &[V], cur: &[V]) -> Vec<Vec<V>> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for &v in supp_el {
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
    mul: Vec<usize>,         // mul[a * 168 + b] = index of gl[a] * gl[b]
    id: usize,               // index of the identity
    // factored action tables (each 168 x 512, L2-resident):
    // left[p * 512 + m] = gl[p] * m,  right[q * 512 + m] = m * gl[q]
    left: Vec<u16>,
    right: Vec<u16>,
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
        let mut left = vec![0u16; 168 * 512];
        let mut right = vec![0u16; 168 * 512];
        for p in 0..168 {
            for m in 0..512u16 {
                left[p * 512 + m as usize] = m3_mul(gl[p], m);
                right[p * 512 + m as usize] = m3_mul(m, gl[p]);
            }
        }
        let mut mul = vec![0usize; 168 * 168];
        for a in 0..168 {
            for b in 0..168 {
                mul[a * 168 + b] = idx[m3_mul(gl[a], gl[b]) as usize] as usize;
            }
        }
        let id = idx[id as usize] as usize;
        Sym { gl, idx, inv, tr, mul, id, left, right }
    }
    /// composition "apply s first, then g". P acts on the LEFT (as P^T or
    /// P^-1) so P_g^T P_s^T = (P_s P_g)^T; Q and R act on the RIGHT so
    /// Q_s^T Q_g^T = (Q_g Q_s)^T: composed = (P_s P_g, Q_g Q_s, R_g R_s).
    /// r = MAX (any R) is resolved to the identity.
    fn compose(&self, s: (usize, usize, usize), g: (usize, usize, usize)) -> (usize, usize, usize) {
        let fix = |r: usize| if r == usize::MAX { self.id } else { r };
        (
            self.mul[fix(s.0) * 168 + fix(g.0)],
            self.mul[fix(g.1) * 168 + fix(s.1)],
            self.mul[fix(g.2) * 168 + fix(s.2)],
        )
    }
    /// vector action of g on one side (A: P^T a Q^T, B: Q^-T b R^T, C: P^-1 c R^-1)
    fn act_vec(&self, g: (usize, usize, usize), side: u8, v: V) -> V {
        let fix = |r: usize| if r == usize::MAX { self.id } else { r };
        match side {
            1 => self.ap(self.tr[g.0], self.tr[g.1], v),
            2 => self.ap(self.tr[self.inv[g.1]], self.tr[fix(g.2)], v),
            _ => self.ap(self.inv[g.0], self.inv[fix(g.2)], v),
        }
    }
    #[inline]
    fn ap(&self, p: usize, q: usize, m: V) -> V {
        self.right[q * 512 + self.left[p * 512 + m as usize] as usize]
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
            // parallel over P: per-thread (best, minimizers), then merge
            // early rejection: the least RREF basis has the lowest possible top
            // pivot, and a candidate's top pivot is the max leading bit of its
            // transformed basis vectors — no row reduction needed to reject.
            let n = s.u.len();
            let parts: Vec<(Vec<V>, Vec<(usize, usize)>)> = (0..168usize)
                .into_par_iter()
                .map(|p| {
                    let tp = self.tr[p];
                    let mut lm = [0u16; 9];
                    for i in 0..n {
                        lm[i] = self.left[tp * 512 + s.u[i] as usize];
                    }
                    let mut best: Option<Vec<V>> = None;
                    let mut best_top: u32 = u32::MAX;
                    let mut mins: Vec<(usize, usize)> = Vec::new();
                    let mut buf = [0u16; 9];
                    for q in 0..168 {
                        let tq = self.tr[q];
                        let rq = &self.right[tq * 512..(tq + 1) * 512];
                        let mut top = 0u32;
                        for i in 0..n {
                            let v = rq[lm[i] as usize];
                            buf[i] = v;
                            top = top.max(16 - v.leading_zeros());
                        }
                        if top > best_top {
                            continue;
                        }
                        let img = rref(&buf[..n]);
                        match &best {
                            Some(b) if img > *b => {}
                            Some(b) if img == *b => mins.push((p, q)),
                            _ => {
                                best_top = top;
                                best = Some(img);
                                mins.clear();
                                mins.push((p, q));
                            }
                        }
                    }
                    (best.unwrap(), mins)
                })
                .collect();
            for (b, mins) in parts {
                match &best_u {
                    Some(bb) if b > *bb => {}
                    Some(bb) if b == *bb => s1.extend(mins),
                    _ => {
                        best_u = Some(b);
                        s1 = mins;
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
            let nv = s.v.len();
            let mut best_top: u32 = u32::MAX;
            for &(p, q) in &s1 {
                let qi = self.tr[self.inv[q]];
                let mut lm = [0u16; 9];
                for i in 0..nv {
                    lm[i] = self.left[qi * 512 + s.v[i] as usize];
                }
                let mut buf = [0u16; 9];
                for r in 0..168 {
                    let tr_r = self.tr[r];
                    let rq = &self.right[tr_r * 512..(tr_r + 1) * 512];
                    let mut top = 0u32;
                    for i in 0..nv {
                        let v = rq[lm[i] as usize];
                        buf[i] = v;
                        top = top.max(16 - v.leading_zeros());
                    }
                    if top > best_top {
                        continue;
                    }
                    let img = rref(&buf[..nv]);
                    match &best_v {
                        Some(b) if img > *b => {}
                        Some(b) if img == *b => s2.push((p, q, r)),
                        _ => {
                            best_top = top;
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
    choice: u8, // 0 = leaf, 1/2/3 = kill on A/B/C, 4/5/6 = split on A/B/C
    phi: V,     // kill: the functional; split: the threshold m (in the low bits)
    leaf: [usize; 3],
    dims: (usize, usize, usize),
}

struct Game {
    t0: Tensor,
    d: usize,
    rank_ub: u32,
    coset: bool,
    splits: bool, // rank-profile case splits (refinement 2)
    want_cert: bool, // when false, skip iso bookkeeping (memory)
    koszul: usize, // 0 = off; else max p for Koszul flattening leaves
    stay: bool,
    par_depth: usize, // adversary branches evaluated in parallel while kills <= par_depth
    sides: Vec<u8>,
    // Wang's verified A-side orbit bounds (arXiv:2603.07280 + our 30x-cascade
    // lifts), keyed by OUR canonical form of the pure-A state. Sound leaf for
    // states with v and x empty: his constraint rows are exactly our u-rows
    // (matmul/r22/koszul_vs_wang.py established the correspondence), so his
    // orbit bound lower-bounds the same quotient tensor. His group includes
    // the A-transpose our sandwich group lacks, so the loader inserts each
    // orbit under both tau-variants.
    wang: Option<HashMap<State, u32>>,
    sym: Option<Sym>,
    stab_cache: Mutex<HashMap<State, Vec<(usize, usize, usize)>>>,
    canon_cache: Mutex<HashMap<State, (State, (usize, usize, usize))>>,
    isos: Mutex<HashMap<State, (State, (usize, usize, usize))>>, // raw child -> (canonical, g)
    memo: HashMap<GState, Proof>,
    lo: Mutex<HashMap<GState, u32>>,
    hi: Mutex<HashMap<GState, u32>>,
    proofs: Mutex<HashMap<GState, Proof>>,
    prof: [AtomicU64; 6], // nanoseconds: canon, stabilizer, phi_reps, quotient+flattening, support, orbit-merge
    n_canon: AtomicU64,
    n_canon_hit: AtomicU64,
    nodes: AtomicU64,
    heartbeat: f64,
    last_beat: AtomicU64,
    node_cap: u64,
    t_start: Instant,
    time_cap: f64,
    capped: AtomicBool,
}

fn ns(t: Instant) -> u64 {
    t.elapsed().as_nanos() as u64
}

impl Game {
    // ---------------- exact game (small n) ----------------
    fn val(&mut self, gs: &GState) -> u32 {
        if let Some(n) = self.memo.get(gs) {
            return n.value;
        }
        let s = gs.s.clone();
        let t = quotient(&self.t0, &s.u, &s.v, &s.x);
        let leaf = flattenings(&t);
        let mut best = *leaf.iter().max().unwrap() as u32;
        if self.coset {
            best = best.max(coset_bound(&t) as u32);
        }
        if self.koszul > 0 {
            best = best.max(koszul_bound(&t, self.koszul) as u32);
        }
        if let Some(wt) = &self.wang {
            if s.v.is_empty() && s.x.is_empty() {
                if let Some(&b) = wt.get(&self.canon(&s)) {
                    best = best.max(b);
                }
            }
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
            let rmin_s = gs.rmin[side as usize - 1];
            let supp = support(&t, side, cur, self.d);
            let supp_el = elements(&supp);
            let (ann, _) = annihilator_free(cur, self.d);
            for phi in elements(&ann).into_iter().filter(|&p| p != 0) {
                if !supp.iter().any(|&sv| dot(phi, sv) == 1) {
                    continue;
                }
                let mut worst = u32::MAX;
                for e in forced_extensions(&supp_el, cur, phi) {
                    if rmin_s > 1 && !coset_has_rank(&e, cur, rmin_s, 3) {
                        continue; // no viable representative: not a legal product coset
                    }
                    let cv = self.val(&GState { s: s.with(side, e), rmin: gs.rmin });
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
            // rank-profile split: some alive product has rank <= m (kill it,
            // adversary over rank-windowed cosets, no phi), or none does
            // (ratchet rmin to m+1 free of charge)
            if self.splits {
                for m in rmin_s..=2 {
                    let mut b1 = u32::MAX; // min over B1 children
                    for e in all_extensions(&supp_el, cur) {
                        if !coset_has_rank(&e, cur, rmin_s, m) {
                            continue;
                        }
                        let cv = self.val(&GState { s: s.with(side, e), rmin: gs.rmin });
                        b1 = b1.min(cv);
                    }
                    let mut r2 = gs.rmin;
                    r2[side as usize - 1] = m + 1;
                    let b2 = self.val(&GState { s: s.clone(), rmin: r2 });
                    let opt = if b1 == u32::MAX { b2 } else { b2.min(1 + b1) };
                    if opt > best {
                        best = opt;
                        choice = 3 + side;
                        best_phi = m as V;
                    }
                }
            }
        }
        self.memo.insert(gs.clone(), Proof { value: best, choice, phi: best_phi, leaf, dims });
        best
    }

    /// canonical representative of a state (identity when symmetry is off)
    fn canon(&self, s: &State) -> State {
        let Some(sym) = &self.sym else { return s.clone() };
        if let Some((c, _)) = self.canon_cache.lock().unwrap().get(s) {
            self.n_canon_hit.fetch_add(1, Ordering::Relaxed);
            return c.clone();
        }
        let t = Instant::now();
        let (c, g) = sym.canon(s);
        self.prof[0].fetch_add(ns(t), Ordering::Relaxed);
        self.n_canon.fetch_add(1, Ordering::Relaxed);
        self.canon_cache.lock().unwrap().insert(s.clone(), (c.clone(), g));
        if self.want_cert {
            self.isos.lock().unwrap().insert(s.clone(), (c.clone(), g));
        }
        c
    }

    /// stabilizer of a canonical state (its own minimizer set), cached
    fn stabilizer(&self, c: &State) -> Vec<(usize, usize, usize)> {
        if let Some(st) = self.stab_cache.lock().unwrap().get(c) {
            return st.clone();
        }
        let t = Instant::now();
        let st = match &self.sym {
            Some(sym) => sym.canon_full(c).2,
            None => vec![],
        };
        self.prof[1].fetch_add(ns(t), Ordering::Relaxed);
        self.stab_cache.lock().unwrap().insert(c.clone(), st.clone());
        st
    }

    // ---------------- decision procedure: val(s) >= k ? ----------------
    fn record(&self, s: &GState, p: Proof) {
        let mut pr = self.proofs.lock().unwrap();
        let cur = pr.get(s).map(|q| q.value).unwrap_or(0);
        if p.value > cur {
            pr.insert(s.clone(), p);
        }
    }
    fn get_lo(&self, s: &GState) -> u32 {
        *self.lo.lock().unwrap().get(s).unwrap_or(&0)
    }
    fn set_lo(&self, s: &GState, v: u32) {
        let mut m = self.lo.lock().unwrap();
        let e = m.entry(s.clone()).or_insert(0);
        if v > *e {
            *e = v;
        }
    }
    fn get_hi(&self, s: &GState) -> u32 {
        *self.hi.lock().unwrap().get(s).unwrap_or(&u32::MAX)
    }
    fn set_hi(&self, s: &GState, v: u32) {
        let mut m = self.hi.lock().unwrap();
        let e = m.entry(s.clone()).or_insert(u32::MAX);
        if v < *e {
            *e = v;
        }
    }

    fn prove(&self, gs: &GState, k: u32) -> bool {
        let s = &gs.s;
        if k == 0 {
            return true;
        }
        let lo = self.get_lo(gs);
        if k <= lo {
            return true;
        }
        let hi = self.get_hi(gs);
        if k >= hi {
            return false;
        }
        let n = self.nodes.fetch_add(1, Ordering::Relaxed) + 1;
        if n > self.node_cap || self.t_start.elapsed().as_secs_f64() > self.time_cap {
            self.capped.store(true, Ordering::Relaxed);
            return false;
        }
        if self.heartbeat > 0.0 {
            // progress heartbeat (stderr): nodes, canonical states, forms, elapsed
            let el = self.t_start.elapsed().as_secs_f64();
            let last_ms = self.last_beat.load(Ordering::Relaxed);
            let el_ms = (el * 1000.0) as u64;
            if el_ms.saturating_sub(last_ms) as f64 >= self.heartbeat * 1000.0
                && self.last_beat.compare_exchange(last_ms, el_ms, Ordering::Relaxed, Ordering::Relaxed).is_ok()
            {
                eprintln!(
                    "c heartbeat {:.0}s: nodes {} states {} failed {} forms {} hits {}",
                    el,
                    n,
                    self.lo.lock().unwrap().len(),
                    self.hi.lock().unwrap().len(),
                    self.n_canon.load(Ordering::Relaxed),
                    self.n_canon_hit.load(Ordering::Relaxed)
                );
            }
        }
        let tq = Instant::now();
        let t = quotient(&self.t0, &s.u, &s.v, &s.x);
        let leaf = flattenings(&t);
        self.prof[3].fetch_add(ns(tq), Ordering::Relaxed);
        let dims = (t.da, t.db, t.dc);
        let mut lb = *leaf.iter().max().unwrap() as u32;
        if self.coset {
            lb = lb.max(coset_bound(&t) as u32);
        }
        if self.koszul > 0 && lb < k {
            let tk = Instant::now();
            lb = lb.max(koszul_bound(&t, self.koszul) as u32);
            self.prof[4].fetch_add(ns(tk), Ordering::Relaxed);
        }
        if lb < k {
            if let Some(wt) = &self.wang {
                if s.v.is_empty() && s.x.is_empty() {
                    if let Some(&b) = wt.get(&self.canon(s)) {
                        lb = lb.max(b);
                    }
                }
            }
        }
        if lb > lo {
            self.set_lo(gs, lb);
            self.record(gs, Proof { value: lb, choice: 0, phi: 0, leaf, dims });
        }
        if lb >= k {
            return true;
        }
        if lb == 0 {
            self.set_hi(gs, 1);
            return false;
        }
        let ub = (dims.0 * dims.1).min(dims.0 * dims.2).min(dims.1 * dims.2) as u32;
        let ub = ub.min(self.rank_ub);
        if k > ub {
            self.set_hi(gs, ub + 1);
            return false;
        }
        // prover: sides ordered by free support dimension (largest first), phi by weight
        let mut sides: Vec<(usize, u8, Vec<V>, Vec<V>)> = Vec::new();
        let is_root0 = s.u.is_empty() && s.v.is_empty() && s.x.is_empty();
        for side in 1..=3u8 {
            if !self.sides.contains(&side) {
                continue; // restricted prover (still a valid lower bound)
            }
            if is_root0 && side != self.sides[0] {
                continue; // WLOG by the S_3 tensor symmetry: the first kill is on the first allowed side
            }
            let cur = s.side(side);
            if cur.len() >= self.d {
                continue;
            }
            let ts = Instant::now();
            let supp = support(&t, side, cur, self.d);
            self.prof[4].fetch_add(ns(ts), Ordering::Relaxed);
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
            let rmin_s = gs.rmin[side as usize - 1];
            let supp_el = elements(&supp);
            let (ann, _) = annihilator_free(&cur, self.d);
            let mut phis: Vec<V> = elements(&ann).into_iter().filter(|&p| p != 0).collect();
            phis.retain(|&p| supp.iter().any(|&sv| dot(p, sv) == 1));
            phis.sort_by_key(|p| p.count_ones());
            if let Some(sym) = &self.sym {
                let tp = Instant::now();
                phis = sym.phi_reps(&stab, side, &phis, is_root);
                self.prof[2].fetch_add(ns(tp), Ordering::Relaxed);
            }
            for phi in phis {
                let mut exts = forced_extensions(&supp_el, &cur, phi);
                if rmin_s > 1 {
                    exts.retain(|e| coset_has_rank(e, &cur, rmin_s, 3));
                }
                // adversary: hardest children first (smallest quick lower bound)
                // group the raw children by the parent's stabilizer orbits: the
                // extension cur + <v> maps under a stabilizer element t to
                // cur + <t v>; key = least coset representative of t v over t.
                // One canonical form per orbit; the others get the composed iso.
                let mut reps: Vec<(State, Vec<(State, (usize, usize, usize))>)> = Vec::new();
                if let Some(sym) = &self.sym {
                    let tc0 = Instant::now();
                    // stabilizer elements deduplicated by the components this side uses
                    let mut elems: Vec<(usize, usize, usize)> = Vec::new();
                    {
                        let mut seen = HashSet::new();
                        for &(p0, q0, r0) in &stab {
                            let rs: Vec<usize> = if r0 == usize::MAX && side != 1 { (0..168).collect() } else { vec![r0] };
                            for r in rs {
                                let k3 = match side {
                                    1 => (p0, q0, usize::MAX),
                                    2 => (usize::MAX, q0, r),
                                    _ => (p0, usize::MAX, r),
                                };
                                if seen.insert(k3) {
                                    elems.push((p0, q0, r));
                                }
                            }
                            if elems.len() > 400_000 {
                                break;
                            }
                        }
                    }
                    let cur_r = rref(&cur);
                    let coset_rep = |mut v: V| {
                        for &o in &cur_r {
                            let pv = 15 - o.leading_zeros();
                            if v >> pv & 1 == 1 {
                                v ^= o;
                            }
                        }
                        v
                    };
                    let mut groups: HashMap<V, (State, Vec<(State, (usize, usize, usize))>)> = HashMap::new();
                    for e in exts {
                        // a vector of e outside cur
                        let v = *e.iter().find(|&&x| coset_rep(x) != 0).unwrap();
                        let mut best_key = coset_rep(v);
                        let mut best_t = (self.sym.as_ref().unwrap().id, self.sym.as_ref().unwrap().id, self.sym.as_ref().unwrap().id);
                        for &t in &elems {
                            let img = coset_rep(sym.act_vec(t, side, v));
                            if img < best_key {
                                best_key = img;
                                best_t = t;
                            }
                        }
                        let raw = s.with(side, e);
                        let entry = groups.entry(best_key).or_insert_with(|| {
                            let mut rows = cur.clone();
                            rows.push(best_key);
                            (s.with(side, rref(&rows)), Vec::new())
                        });
                        entry.1.push((raw, best_t));
                    }
                    reps = groups.into_values().collect();
                    self.prof[5].fetch_add(ns(tc0), Ordering::Relaxed);
                    // canonicalize the representatives in parallel (cache misses only)
                    let need: Vec<State> = {
                        let cc = self.canon_cache.lock().unwrap();
                        reps.iter().map(|(r, _)| r.clone()).filter(|r| !cc.contains_key(r)).collect()
                    };
                    let tcn = Instant::now();
                    let done: Vec<(State, (State, (usize, usize, usize)))> =
                        need.par_iter().map(|r| (r.clone(), sym.canon(r))).collect();
                    self.prof[0].fetch_add(ns(tcn), Ordering::Relaxed);
                    self.n_canon.fetch_add(done.len() as u64, Ordering::Relaxed);
                    {
                        let mut cc = self.canon_cache.lock().unwrap();
                        for (r, cg) in &done {
                            cc.insert(r.clone(), cg.clone());
                        }
                        if self.want_cert {
                            let mut is = self.isos.lock().unwrap();
                            for (r, cg) in done {
                                is.insert(r, cg);
                            }
                        }
                    }
                } else {
                    reps = exts.into_iter().map(|e| { let raw = s.with(side, e); (raw.clone(), vec![(raw, (0, 0, 0))]) }).collect();
                }
                let mut kids: Vec<(u32, GState)> = Vec::new();
                for (rep, members) in reps {
                    let c = self.canon(&rep);
                    if self.want_cert {
                        if let Some(sym) = &self.sym {
                            let g_rep = self.canon_cache.lock().unwrap()[&rep].1;
                            let mut is = self.isos.lock().unwrap();
                            for (raw, t) in members {
                                if !is.contains_key(&raw) {
                                    is.insert(raw, (c.clone(), sym.compose(t, g_rep)));
                                }
                            }
                        }
                    }
                    let gc = GState { s: c, rmin: gs.rmin };
                    let known = self.get_lo(&gc);
                    let q = if known >= k - 1 {
                        known
                    } else {
                        let tq = Instant::now();
                        let tc = quotient(&self.t0, &gc.s.u, &gc.s.v, &gc.s.x);
                        let f = *flattenings(&tc).iter().max().unwrap() as u32;
                        self.prof[3].fetch_add(ns(tq), Ordering::Relaxed);
                        f
                    };
                    kids.push((q, gc));
                }
                kids.sort_by_key(|(q, _)| *q);
                kids.dedup_by(|a, b| a.1 == b.1);
                let kills = s.u.len() + s.v.len() + s.x.len();
                let all_ok = if kills <= self.par_depth && kids.len() >= 2 {
                    // adversary branches in parallel (all must succeed; rayon
                    // stops scheduling new ones after the first failure)
                    kids.par_iter().all(|(_, c)| self.prove(c, k - 1))
                } else {
                    let mut ok = true;
                    for (_, c) in &kids {
                        if !self.prove(c, k - 1) {
                            ok = false;
                            break;
                        }
                    }
                    ok
                };
                if self.capped.load(Ordering::Relaxed) {
                    return false;
                }
                if all_ok {
                    self.set_lo(gs, k);
                    self.record(gs, Proof { value: k, choice: side, phi, leaf, dims });
                    return true;
                }
            }
            // rank-profile split (refinement 2): either some alive product's
            // side-s vector has rank in [rmin_s, m] — kill one, adversary over
            // ALL rank-windowed support cosets (no functional) — or none does
            // and rmin_s ratchets to m+1 free of charge.
            if self.splits {
                for m in rmin_s..=2 {
                    let mut seen_kids: HashSet<GState> = HashSet::new();
                    let mut b1_kids: Vec<(u32, GState)> = Vec::new();
                    let mut viable = true;
                    for e in all_extensions(&supp_el, &cur) {
                        if !coset_has_rank(&e, &cur, rmin_s, m) {
                            continue;
                        }
                        let c = self.canon(&s.with(side, e));
                        let g = GState { s: c, rmin: gs.rmin };
                        if !seen_kids.insert(g.clone()) {
                            continue;
                        }
                        let q = self.get_lo(&g); // snapshot ONCE: sorting by a live map is not a total order
                        b1_kids.push((q, g));
                    }
                    b1_kids.sort_by_key(|(q, _)| *q);
                    for (_, g) in &b1_kids {
                        if !self.prove(g, k - 1) {
                            viable = false;
                            break;
                        }
                    }
                    if self.capped.load(Ordering::Relaxed) {
                        return false;
                    }
                    if !viable {
                        continue;
                    }
                    let mut r2 = gs.rmin;
                    r2[side as usize - 1] = m + 1;
                    let b2 = GState { s: s.clone(), rmin: r2 };
                    if self.prove(&b2, k) {
                        self.set_lo(gs, k);
                        self.record(gs, Proof { value: k, choice: 3 + side, phi: m as V, leaf, dims });
                        return true;
                    }
                }
            }
        }
        self.set_hi(gs, k);
        false
    }
}

fn key(g: &GState) -> String {
    let f = |v: &[V]| v.iter().map(|x| format!("{x:x}")).collect::<Vec<_>>().join(",");
    format!("{}|{}|{}|{},{},{}", f(&g.s.u), f(&g.s.v), f(&g.s.x), g.rmin[0], g.rmin[1], g.rmin[2])
}

/// certificate DAG from the proof records: chosen side/phi at prover nodes,
/// ALL forced children at adversary nodes, leaf facts
fn certificate(g: &Game, n: usize, root: &GState, proofs: &HashMap<GState, Proof>) -> String {
    let mut out = String::new();
    let mut seen = HashSet::new();
    let mut stack = vec![root.clone()];
    let mut lines = Vec::new();
    while let Some(gsn) = stack.pop() {
        if !seen.insert(key(&gsn)) {
            continue;
        }
        let s = &gsn.s;
        let node = proofs.get(&gsn).expect("proof record missing");
        let mut line = String::new();
        write!(
            line,
            "{{\"key\":\"{}\",\"dims\":[{},{},{}],\"value\":{},\"choice\":{},\"phi\":{},\"leaf\":[{},{},{}]",
            key(&gsn), node.dims.0, node.dims.1, node.dims.2, node.value, node.choice, node.phi, node.leaf[0], node.leaf[1], node.leaf[2]
        )
        .unwrap();
        let emit_children = |g: &Game, exts: Vec<Vec<V>>, side: u8, rmin: Rmin, stack: &mut Vec<GState>| -> Vec<String> {
            let mut ks = Vec::new();
            for e in exts {
                let child = s.with(side, e);
                let iso = g.isos.lock().unwrap().get(&child).cloned();
                match iso {
                    Some((c, gg)) if g.sym.is_some() => {
                        let sym = g.sym.as_ref().unwrap();
                        let gc = GState { s: c, rmin };
                        ks.push(format!(
                            "{{\"raw\":\"{}\",\"canon\":\"{}\",\"g\":[{},{},{}]}}",
                            key(&GState { s: child, rmin }), key(&gc), sym.gl[gg.0], sym.gl[gg.1], sym.gl[gg.2]
                        ));
                        stack.push(gc);
                    }
                    _ => {
                        let gc = GState { s: child, rmin };
                        ks.push(format!("{{\"raw\":\"{}\"}}", key(&gc)));
                        stack.push(gc);
                    }
                }
            }
            ks
        };
        if node.choice >= 4 {
            // split node: B1 = rank-windowed cosets (no functional); B2 = ratcheted rmin
            let side = node.choice - 3;
            let m = node.phi as u8;
            let cur = s.side(side);
            let t = quotient(&g.t0, &s.u, &s.v, &s.x);
            let supp = support(&t, side, cur, g.d);
            let rs = gsn.rmin[side as usize - 1];
            let exts: Vec<Vec<V>> = all_extensions(&elements(&supp), cur)
                .into_iter()
                .filter(|e| coset_has_rank(e, cur, rs, m))
                .collect();
            let ks = emit_children(g, exts, side, gsn.rmin, &mut stack);
            let mut r2 = gsn.rmin;
            r2[side as usize - 1] = m + 1;
            let b2 = GState { s: s.clone(), rmin: r2 };
            write!(line, ",\"b1\":[{}],\"b2\":\"{}\"", ks.join(","), key(&b2)).unwrap();
            stack.push(b2);
        } else if node.choice != 0 {
            let cur = s.side(node.choice);
            let t = quotient(&g.t0, &s.u, &s.v, &s.x);
            let supp = support(&t, node.choice, cur, g.d);
            let rs = gsn.rmin[node.choice as usize - 1];
            let mut exts = forced_extensions(&elements(&supp), cur, node.phi);
            if rs > 1 {
                exts.retain(|e| coset_has_rank(e, cur, rs, 3));
            }
            let ks = emit_children(g, exts, node.choice, gsn.rmin, &mut stack);
            write!(line, ",\"children\":[{}]", ks.join(",")).unwrap();
        }
        line.push('}');
        lines.push(line);
    }
    writeln!(out, "{{\"n\":{n},\"coset\":{},\"koszul\":{},\"root\":\"{}\",\"nodes\":[", g.coset, g.koszul, key(root)).unwrap();
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
        splits: flag("--splits"),
        want_cert: get("--cert").is_some(),
        koszul: get("--koszul").and_then(|v| v.parse().ok()).unwrap_or(0),
        stay: flag("--stay"),
        sides: {
            let spec = if flag("--onesided") { "A".to_string() } else { get("--sides").unwrap_or_else(|| "ABC".to_string()) };
            spec.chars().filter_map(|ch| match ch { 'A' => Some(1u8), 'B' => Some(2), 'C' => Some(3), _ => None }).collect()
        },
        wang: None,
        sym,
        par_depth: get("--par").and_then(|v| v.parse().ok()).unwrap_or(0),
        stab_cache: Mutex::new(HashMap::new()),
        canon_cache: Mutex::new(HashMap::new()),
        isos: Mutex::new(HashMap::new()),
        memo: HashMap::new(),
        lo: Mutex::new(HashMap::new()),
        hi: Mutex::new(HashMap::new()),
        proofs: Mutex::new(HashMap::new()),
        prof: [AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0), AtomicU64::new(0)],
        n_canon: AtomicU64::new(0),
        n_canon_hit: AtomicU64::new(0),
        nodes: AtomicU64::new(0),
        heartbeat: get("--heartbeat").and_then(|v| v.parse().ok()).unwrap_or(0.0),
        last_beat: AtomicU64::new(0),
        node_cap: get("--nodes").and_then(|v| v.parse().ok()).unwrap_or(50_000_000),
        t_start: Instant::now(),
        time_cap: get("--time").and_then(|v| v.parse().ok()).unwrap_or(600.0),
        capped: AtomicBool::new(false),
    };
    if let Some(path) = get("--wang-table") {
        // <bound>:<row,row,...> per line; insert both tau-variants (his
        // A-side group has the transpose, our canon group does not).
        let ts = Instant::now();
        let mut map: HashMap<State, u32> = HashMap::new();
        let txt = std::fs::read_to_string(&path).expect("--wang-table file");
        let mut n_entries = 0usize;
        for line in txt.lines() {
            let Some((b, rows)) = line.split_once(':') else { continue };
            let bound: u32 = b.trim().parse().expect("table bound");
            let rows: Vec<V> = rows
                .split(',')
                .filter(|r| !r.trim().is_empty())
                .map(|r| r.trim().parse::<V>().expect("table row"))
                .collect();
            n_entries += 1;
            for variant in [rows.clone(), rows.iter().map(|&r| m3_tr(r)).collect::<Vec<V>>()] {
                let st = State { u: rref(&variant), v: vec![], x: vec![] };
                let key = g.canon(&st);
                let e = map.entry(key).or_insert(0);
                *e = (*e).max(bound);
            }
        }
        eprintln!(
            "wang table: {} orbits -> {} canonical keys ({:.1}s)",
            n_entries,
            map.len(),
            ts.elapsed().as_secs_f64()
        );
        g.wang = Some(map);
    }
    let root = if let Some(spec) = get("--root-u") {
        let rows: Vec<V> = spec.split(',').map(|r| r.trim().parse::<V>().expect("--root-u row")).collect();
        let u = rref(&rows);
        assert_eq!(u.len(), rows.len(), "--root-u rows must be independent");
        eprintln!("root state: u = {:?} (dim {})", u, u.len());
        GState { s: State { u, v: vec![], x: vec![] }, rmin: [1, 1, 1] }
    } else {
        GState { s: State { u: vec![], v: vec![], x: vec![] }, rmin: [1, 1, 1] }
    };
    let scope = if root.s.u.is_empty() && root.s.v.is_empty() && root.s.x.is_empty() {
        format!("rank_F2(<{n},{n},{n}>)")
    } else {
        format!("rank_F2(<{n},{n},{n}> | A-restricted u={:?})", root.s.u)
    };
    if flag("--root-bounds") {
        let t = &g.t0;
        println!(
            "root flattenings {:?}; coset {}; koszul per p: {:?}",
            flattenings(t),
            coset_bound(t),
            (1..=(d - 2)).map(|p| koszul_side(t, p)).collect::<Vec<_>>()
        );
        return;
    }
    if flag("--bench-canon") {
        // microbenchmark: canonical form of random one-sided states per dimension
        let sym = g.sym.as_ref().expect("--bench-canon needs --sym");
        let mut seed = 12345u64;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for dim in 1..=8usize {
            let mut states = Vec::new();
            while states.len() < 10 {
                let rows: Vec<V> = (0..dim).map(|_| (rnd() % 511 + 1) as V).collect();
                let r = rref(&rows);
                if r.len() == dim { states.push(State { u: r, v: vec![], x: vec![] }); }
            }
            let t = Instant::now();
            let mut stab_sizes = 0usize;
            for st in &states {
                let (_, _, s3) = sym.canon_full(st);
                stab_sizes += s3.len();
            }
            let per = t.elapsed().as_secs_f64() / states.len() as f64 * 1000.0;
            println!("dim {dim}: canon_full {per:.2} ms/state (parallel stage 1), mean |stabilizer| {:.0}", stab_sizes as f64 / states.len() as f64);
        }
        return;
    }
    if flag("--ladder") {
        let from: u32 = get("--from").and_then(|v| v.parse().ok()).unwrap_or(1);
        let to: u32 = get("--to").and_then(|v| v.parse().ok()).unwrap_or(u32::MAX);
        let mut proven = 0u32;
        let mut k = from;
        loop {
            if k > to {
                println!("stopping at --to {to}");
                break;
            }
            let t = Instant::now();
            let ok = g.prove(&root, k);
            if g.capped.load(Ordering::Relaxed) {
                println!(
                    "k={k}: CAP (nodes {} / {:.1}s) — last proven {proven}",
                    g.nodes.load(Ordering::Relaxed),
                    g.t_start.elapsed().as_secs_f64()
                );
                break;
            }
            if ok {
                proven = k;
                println!(
                    "k={k}: PROVED val >= {k}  (+{:.2}s, {} nodes total, {} states)",
                    t.elapsed().as_secs_f64(),
                    g.nodes.load(Ordering::Relaxed),
                    g.lo.lock().unwrap().len()
                );
                k += 1;
            } else {
                println!(
                    "k={k}: FAILS — exact game value = {proven}  ({} nodes, {:.2}s)",
                    g.nodes.load(Ordering::Relaxed),
                    g.t_start.elapsed().as_secs_f64()
                );
                break;
            }
        }
        println!(
"=> {scope} >= {proven} by the substitution game{}",
            if coset { " + coset bound" } else { "" }
        );
        if flag("--prof") {
            let tot = g.t_start.elapsed().as_secs_f64();
            let pf = |i: usize| g.prof[i].load(Ordering::Relaxed) as f64 / 1e9;
            println!(
                "profile: total {tot:.1}s | canon {:.1}s thread-time ({} computed, {} cache hits) | stabilizer {:.1}s | phi_reps {:.1}s | quotient+flat {:.1}s | support {:.1}s | orbit-merge {:.1}s | states lo={} hi={} stab_cache={}",
                pf(0), g.n_canon.load(Ordering::Relaxed), g.n_canon_hit.load(Ordering::Relaxed), pf(1), pf(2), pf(3), pf(4), pf(5),
                g.lo.lock().unwrap().len(), g.hi.lock().unwrap().len(), g.stab_cache.lock().unwrap().len()
            );
        }
        if let Some(path) = cert {
            if proven > 0 {
                let proofs = g.proofs.lock().unwrap().clone();
                let max_records: usize = get("--cert-max").and_then(|v| v.parse().ok()).unwrap_or(3_000_000);
                if proofs.len() > max_records {
                    println!("certificate skipped: {} proof records (> --cert-max {})", proofs.len(), max_records);
                } else {
                    let c = certificate(&g, n, &root, &proofs);
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
"=> {scope} >= {value} by the substitution game{}",
            if coset { " + coset bound" } else { "" }
        );
        if let Some(path) = cert {
            let c = certificate(&g, n, &root, &g.memo);
            std::fs::write(&path, &c).expect("write cert");
            println!("certificate: {} ({} bytes)", path, c.len());
        }
    }
}
