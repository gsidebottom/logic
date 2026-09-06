//! Exact-or-sound rank of a matrix PENCIL over F_2 (a 2 x m x n tensor
//! sA + tB), via the Kronecker canonical form (2026-09-02).
//!
//! rank(sA + tB) = sum over Kronecker blocks:
//!   L_eps (eps x (eps+1))      -> rank of L_eps over F_2 (L_0 is a zero column: 0)
//!   L_eta^T ((eta+1) x eta)    -> same as L_eta (transpose)
//! Over F_2 even the L blocks exceed Ja'Ja''s eps + 1 for eps >= 3 (L_3 has
//! rank 5, brute force 2026-09-02: it is the multiplication of a linear
//! form by a degree-(eps-1) polynomial, which needs eps + 1 evaluation
//! points and F_2 has three), so they are brute-forced for eps <= L_BRUTE_MAX
//! and bounded below by eps + 1 beyond.
//!   regular block for an elementary divisor q = p^k of degree D
//!                              -> rank of the D x D pencil (I, C_q)
//! The L-block values are Ja'Ja''s (field-independent); the regular
//! block values over F_2 are NOT the textbook n + (#non-split invariant
//! factors) (an irreducible cubic contributes +2, not +1 — brute force
//! 2026-09-02), so they are computed here exactly by brute force for
//! D <= BRUTE_MAX (min over X of rank X + rank(I+X) + rank(C+X), cached)
//! and replaced by the sound lower bound D + [q not squarefree-split]
//! above that (a pencil (I, A) has rank D iff A is diagonalizable).
//! Block additivity is verified against brute force in the tests.
//!
//! Matrices are rows of bits (`u16`, column j = bit j), m rows, n columns,
//! m, n <= 9.  Polynomials over F_2 are `u64` bit masks (bit i = x^i).

use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

pub const BRUTE_MAX: usize = 5;
pub const L_BRUTE_MAX: usize = 4;

// ---------------------------------------------------------------- F_2 linear algebra

fn rank_rows_u128(rows: &mut Vec<u128>) -> usize {
    let mut rank = 0;
    let mut bit = 127i32;
    while bit >= 0 && rank < rows.len() {
        if let Some(p) = (rank..rows.len()).find(|&i| rows[i] >> bit & 1 == 1) {
            rows.swap(rank, p);
            for i in 0..rows.len() {
                if i != rank && rows[i] >> bit & 1 == 1 {
                    rows[i] ^= rows[rank];
                }
            }
            rank += 1;
        }
        bit -= 1;
    }
    rank
}

pub fn rank_u16(rows: &[u16]) -> usize {
    let mut r: Vec<u128> = rows.iter().map(|&x| x as u128).collect();
    rank_rows_u128(&mut r)
}

fn transpose(rows: &[u16], m: usize, n: usize) -> Vec<u16> {
    let mut t = vec![0u16; n];
    for i in 0..m {
        for j in 0..n {
            if rows[i] >> j & 1 == 1 {
                t[j] |= 1 << i;
            }
        }
    }
    t
}

/// nullity of the k-th block-Toeplitz matrix
///   [ A          ]
///   [ B  A       ]   ((k+1) m  x  k n)
///   [    B  A    ]
///   [       .. B ]
fn toeplitz_nullity(a: &[u16], b: &[u16], m: usize, n: usize, k: usize) -> usize {
    let cols = k * n;
    assert!(cols <= 128);
    let mut rows: Vec<u128> = Vec::with_capacity((k + 1) * m);
    for blk in 0..=k {
        for i in 0..m {
            let mut r = 0u128;
            if blk < k {
                r |= (a[i] as u128) << (blk * n);
            }
            if blk >= 1 {
                r |= (b[i] as u128) << ((blk - 1) * n);
            }
            rows.push(r);
        }
    }
    cols - rank_rows_u128(&mut rows)
}

/// column minimal indices (multiset of eps) of the pencil sA + tB
fn minimal_indices(a: &[u16], b: &[u16], m: usize, n: usize) -> Vec<usize> {
    // d_k = sum_{eps < k} (k - eps) n_eps  =>  Delta_k = d_k - d_{k-1} = #{eps <= k-1}
    let mut d = vec![0usize];
    for k in 1..=(n + 1) {
        d.push(toeplitz_nullity(a, b, m, n, k));
    }
    let mut out = Vec::new();
    let mut prev_delta = 0usize;
    for k in 1..=(n + 1) {
        let delta = d[k] - d[k - 1];
        let n_eps = delta - prev_delta; // number of L_{k-1}
        for _ in 0..n_eps {
            out.push(k - 1);
        }
        prev_delta = delta;
    }
    out
}

// ---------------------------------------------------------------- F_2[x] polynomials

fn pdeg(p: u64) -> i32 {
    63 - p.leading_zeros() as i32
}

fn pmul(a: u64, b: u64) -> u64 {
    let mut r = 0u64;
    let mut a = a;
    let mut b = b;
    while b != 0 {
        if b & 1 == 1 {
            r ^= a;
        }
        a <<= 1;
        b >>= 1;
    }
    r
}

/// (quotient, remainder) of a by b, b != 0
fn pdivmod(a: u64, b: u64) -> (u64, u64) {
    let db = pdeg(b);
    let mut q = 0u64;
    let mut r = a;
    while r != 0 && pdeg(r) >= db {
        let s = (pdeg(r) - db) as u32;
        q |= 1u64 << s;
        r ^= b << s;
    }
    (q, r)
}

/// irreducible polynomials over F_2 up to degree `maxdeg`, ascending
fn irreducibles(maxdeg: usize) -> Vec<u64> {
    let mut out: Vec<u64> = Vec::new();
    for d in 1..=maxdeg {
        for p in (1u64 << d)..(1u64 << (d + 1)) {
            let mut ok = true;
            for &q in &out {
                if (pdeg(q) as usize) * 2 > d {
                    break;
                }
                if pdivmod(p, q).1 == 0 {
                    ok = false;
                    break;
                }
            }
            if ok {
                out.push(p);
            }
        }
    }
    out
}

/// factor a nonzero polynomial into (irreducible, multiplicity)
fn factor(p: u64) -> Vec<(u64, usize)> {
    let mut out = Vec::new();
    let mut p = p;
    let d = pdeg(p) as usize;
    if d == 0 {
        return out;
    }
    for q in irreducibles(d) {
        if (pdeg(q) as usize) * 2 > pdeg(p) as usize && p != q {
            break;
        }
        let mut k = 0;
        loop {
            let (qq, r) = pdivmod(p, q);
            if r != 0 {
                break;
            }
            p = qq;
            k += 1;
        }
        if k > 0 {
            out.push((q, k));
        }
        if pdeg(p) == 0 {
            break;
        }
    }
    if pdeg(p) > 0 {
        out.push((p, 1)); // remaining irreducible
    }
    out
}

/// Smith normal form over F_2[x] of an m x n polynomial matrix; returns
/// the nonzero invariant factors d_1 | d_2 | ... (monic is automatic).
fn smith_invariants(mut mat: Vec<Vec<u64>>, m: usize, n: usize) -> Vec<u64> {
    let mut inv = Vec::new();
    let mut r0 = 0usize;
    while r0 < m && r0 < n {
        // pivot: nonzero entry of minimal degree in the submatrix
        let mut best: Option<(usize, usize, i32)> = None;
        for i in r0..m {
            for j in r0..n {
                if mat[i][j] != 0 {
                    let d = pdeg(mat[i][j]);
                    if best.map_or(true, |b| d < b.2) {
                        best = Some((i, j, d));
                    }
                }
            }
        }
        let Some((pi, pj, _)) = best else { break };
        mat.swap(r0, pi);
        for row in mat.iter_mut() {
            row.swap(r0, pj);
        }
        loop {
            let piv = mat[r0][r0];
            let mut dirty = false;
            // clear column r0
            for i in (r0 + 1)..m {
                if mat[i][r0] != 0 {
                    let (q, _) = pdivmod(mat[i][r0], piv);
                    for j in r0..n {
                        let sub = pmul(q, mat[r0][j]);
                        mat[i][j] ^= sub;
                    }
                    if mat[i][r0] != 0 {
                        // remainder of smaller degree: make it the pivot
                        mat.swap(r0, i);
                        dirty = true;
                        break;
                    }
                }
            }
            if dirty {
                continue;
            }
            // clear row r0
            for j in (r0 + 1)..n {
                if mat[r0][j] != 0 {
                    let (q, _) = pdivmod(mat[r0][j], piv);
                    for i in r0..m {
                        let sub = pmul(q, mat[i][r0]);
                        mat[i][j] ^= sub;
                    }
                    if mat[r0][j] != 0 {
                        for row in mat.iter_mut() {
                            row.swap(r0, j);
                        }
                        dirty = true;
                        break;
                    }
                }
            }
            if dirty {
                continue;
            }
            // divisibility of the rest by the pivot
            let mut fixed = false;
            'outer: for i in (r0 + 1)..m {
                for j in (r0 + 1)..n {
                    if mat[i][j] != 0 && pdivmod(mat[i][j], piv).1 != 0 {
                        // add row i to row r0 and redo
                        for jj in r0..n {
                            let v = mat[i][jj];
                            mat[r0][jj] ^= v;
                        }
                        fixed = true;
                        break 'outer;
                    }
                }
            }
            if fixed {
                continue;
            }
            break;
        }
        inv.push(mat[r0][r0]);
        r0 += 1;
    }
    inv
}

// ---------------------------------------------------------------- Kronecker structure

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Kronecker {
    pub eps: Vec<usize>,           // L_eps blocks
    pub eta: Vec<usize>,           // L_eta^T blocks
    pub finite: Vec<(u64, usize)>, // elementary divisors p^k (p irreducible)
    pub infinite: Vec<usize>,      // nilpotent blocks N_k (eigenvalue "infinity")
    pub regular_dim: usize,
}

pub fn kronecker(a: &[u16], b: &[u16], m: usize, n: usize) -> Kronecker {
    let eps = minimal_indices(a, b, m, n);
    let (at, bt) = (transpose(a, m, n), transpose(b, m, n));
    let eta = minimal_indices(&at, &bt, n, m);
    let se: usize = eps.iter().sum();
    let sh: usize = eta.iter().sum();
    let regular_dim = m
        .checked_sub(se + sh + eta.len())
        .expect("row count inconsistent with minimal indices");
    assert_eq!(regular_dim, n - (se + eps.len()) - sh, "column count inconsistent");
    // finite elementary divisors: Smith form of A + xB
    let mat: Vec<Vec<u64>> = (0..m)
        .map(|i| (0..n).map(|j| ((a[i] >> j & 1) as u64) | (((b[i] >> j & 1) as u64) << 1)).collect())
        .collect();
    let mut finite = Vec::new();
    for d in smith_invariants(mat, m, n) {
        for (p, k) in factor(d) {
            finite.push((p, k));
        }
    }
    // infinite: x-power factors of the Smith form of xA + B
    let mat2: Vec<Vec<u64>> = (0..m)
        .map(|i| (0..n).map(|j| (((a[i] >> j & 1) as u64) << 1) | ((b[i] >> j & 1) as u64)).collect())
        .collect();
    let mut infinite = Vec::new();
    for d in smith_invariants(mat2, m, n) {
        let k = d.trailing_zeros() as usize;
        if d != 0 && k > 0 {
            infinite.push(k);
        }
    }
    let fin_deg: usize = finite.iter().map(|&(p, k)| pdeg(p) as usize * k).sum();
    let inf_deg: usize = infinite.iter().sum();
    assert_eq!(fin_deg + inf_deg, regular_dim, "elementary divisors do not fill the regular part");
    Kronecker { eps, eta, finite, infinite, regular_dim }
}

// ---------------------------------------------------------------- block ranks

/// companion matrix of a monic polynomial q of degree D (rows as bits)
fn companion(q: u64) -> Vec<u16> {
    let d = pdeg(q) as usize;
    let mut c = vec![0u16; d];
    for i in 0..d - 1 {
        c[i + 1] |= 1 << i; // subdiagonal ones: x * e_i = e_{i+1}
    }
    // last column: x^D = sum_{i<D} q_i x^i
    for i in 0..d {
        if q >> i & 1 == 1 {
            c[i] |= 1 << (d - 1);
        }
    }
    c
}

/// exact rank of the D x D pencil (I, C) by brute force over X
fn regular_pencil_brute(c: &[u16], d: usize) -> usize {
    let ident: Vec<u16> = (0..d).map(|i| 1u16 << i).collect();
    let mut best = usize::MAX;
    let total = 1u64 << (d * d);
    let mask = (1u16 << d) - 1;
    for bits in 0..total {
        let x: Vec<u16> = (0..d).map(|i| ((bits >> (i * d)) as u16) & mask).collect();
        let r = rank_u16(&x);
        if r >= best {
            continue;
        }
        let ix: Vec<u16> = (0..d).map(|i| ident[i] ^ x[i]).collect();
        let r2 = rank_u16(&ix);
        if r + r2 >= best {
            continue;
        }
        let cx: Vec<u16> = (0..d).map(|i| c[i] ^ x[i]).collect();
        let v = r + r2 + rank_u16(&cx);
        if v < best {
            best = v;
        }
    }
    best
}

fn block_cache() -> &'static Mutex<HashMap<u64, usize>> {
    static C: OnceLock<Mutex<HashMap<u64, usize>>> = OnceLock::new();
    C.get_or_init(|| Mutex::new(HashMap::new()))
}

/// q not a product of distinct linear factors over F_2 => (I, C_q) is not
/// diagonalizable => rank >= D + 1 (a rank-D decomposition would diagonalize)
fn squarefree_split(q: u64) -> bool {
    // q | x(x+1) up to units: divisors of x^2 + x = 0b110
    q == 0b10 || q == 0b11 || q == 0b110 || q == 1
}

/// rank (exact for D <= BRUTE_MAX, else sound lower bound) of the regular
/// block with elementary divisor q = p^k of degree D
pub fn regular_block_rank(q: u64) -> (usize, bool) {
    let d = pdeg(q) as usize;
    if squarefree_split(q) {
        return (d, true);
    }
    if d <= BRUTE_MAX {
        if let Some(&v) = block_cache().lock().unwrap().get(&q) {
            return (v, true);
        }
        let v = regular_pencil_brute(&companion(q), d);
        block_cache().lock().unwrap().insert(q, v);
        return (v, true);
    }
    (d + 1, false)
}

/// the eps x (eps+1) block L_eps: A = [I 0], B = [0 I]
fn l_block(eps: usize) -> (Vec<u16>, Vec<u16>) {
    let a: Vec<u16> = (0..eps).map(|i| 1u16 << i).collect();
    let b: Vec<u16> = (0..eps).map(|i| 1u16 << (i + 1)).collect();
    (a, b)
}

fn l_cache() -> &'static Mutex<HashMap<usize, usize>> {
    static C: OnceLock<Mutex<HashMap<usize, usize>>> = OnceLock::new();
    C.get_or_init(|| Mutex::new(HashMap::new()))
}

/// rank of L_eps over F_2: exact for eps <= L_BRUTE_MAX, else the sound
/// lower bound eps + 1 (the algebraically-closed value)
pub fn l_block_rank(eps: usize) -> (usize, bool) {
    if eps == 0 {
        return (0, true);
    }
    if eps <= L_BRUTE_MAX {
        if let Some(&v) = l_cache().lock().unwrap().get(&eps) {
            return (v, true);
        }
        let (a, b) = l_block(eps);
        let v = pencil_rank_brute(&a, &b, eps, eps + 1);
        l_cache().lock().unwrap().insert(eps, v);
        return (v, true);
    }
    (eps + 1, false)
}

fn ppow(p: u64, k: usize) -> u64 {
    let mut r = 1u64;
    for _ in 0..k {
        r = pmul(r, p);
    }
    r
}

/// (side-dimension s, F_2 excess e) per block: the block's rank is
/// s + e, where s = its Ja'Ja' (algebraically closed) value and e >= 0.
fn block_profile(kr: &Kronecker) -> Vec<(usize, usize)> {
    let mut out = Vec::new();
    for &e in kr.eps.iter().chain(kr.eta.iter()) {
        if e > 0 {
            let (v, _) = l_block_rank(e);
            out.push((e + 1, v - (e + 1)));
        }
    }
    for &(p, k) in &kr.finite {
        let q = ppow(p, k);
        let d = pdeg(q) as usize;
        let (v, _) = regular_block_rank(q);
        out.push((d, v - d));
    }
    for &k in &kr.infinite {
        let (v, _) = regular_block_rank(1u64 << k);
        out.push((k, v - k));
    }
    out
}

/// SOUND lower bound on the rank of the pencil sA + tB over F_2.
///
/// Block additivity FAILS over F_2 ((x+1)^2 (+) N_2 has rank 5, not 3+3:
/// brute force 2026-09-02), so block ranks cannot be summed. What is
/// sound is the substitution argument across blocks: rank(P (+) Q) >=
/// rank(P) + (a side dimension of Q), giving
///     sum_i s_i + max_i e_i
/// with s_i the Ja'Ja' value of block i (its rank over the algebraic
/// closure, which is also its larger side dimension) and e_i its F_2
/// excess from the brute-forced tables (0 where unknown). Pencils with
/// m*n <= BRUTE_WHOLE_BITS are ranked exactly by brute force instead.
pub const BRUTE_WHOLE_BITS: usize = 16;

pub fn pencil_rank_lb(a: &[u16], b: &[u16], m: usize, n: usize) -> usize {
    if m * n <= BRUTE_WHOLE_BITS {
        return pencil_rank_brute(a, b, m, n);
    }
    let kr = kronecker(a, b, m, n);
    let prof = block_profile(&kr);
    let s: usize = prof.iter().map(|x| x.0).sum();
    let e = prof.iter().map(|x| x.1).max().unwrap_or(0);
    s + e
}

/// OPTIMISTIC block-additive sum (NOT sound over F_2 in general; for
/// measuring the ceiling of the pencil leaf only).
pub fn pencil_rank_additive(a: &[u16], b: &[u16], m: usize, n: usize) -> usize {
    let kr = kronecker(a, b, m, n);
    block_profile(&kr).iter().map(|x| x.0 + x.1).sum()
}

/// Kept for single-block / structured use: the additive value with an
/// exactness flag (exact only when every block is tabulated AND there is
/// at most one block, or the caller knows additivity holds).
pub fn pencil_rank(a: &[u16], b: &[u16], m: usize, n: usize) -> (usize, bool) {
    let kr = kronecker(a, b, m, n);
    let prof = block_profile(&kr);
    let tabulated = kr.eps.iter().chain(kr.eta.iter()).all(|&e| e <= L_BRUTE_MAX)
        && kr.finite.iter().all(|&(p, k)| pdeg(ppow(p, k)) as usize <= BRUTE_MAX)
        && kr.infinite.iter().all(|&k| k <= BRUTE_MAX);
    let nblocks = prof.len();
    (prof.iter().map(|x| x.0 + x.1).sum(), tabulated && nblocks <= 1)
}

/// brute-force exact rank of a general pencil: min over X of
/// rank X + rank(A + X) + rank(B + X)  (m*n <= 25)
pub fn pencil_rank_brute(a: &[u16], b: &[u16], m: usize, n: usize) -> usize {
    assert!(m * n <= 25);
    let mut best = usize::MAX;
    let mask = (1u16 << n) - 1;
    for bits in 0u64..(1u64 << (m * n)) {
        let x: Vec<u16> = (0..m).map(|i| ((bits >> (i * n)) as u16) & mask).collect();
        let r = rank_u16(&x);
        if r >= best {
            continue;
        }
        let ax: Vec<u16> = (0..m).map(|i| a[i] ^ x[i]).collect();
        let r2 = rank_u16(&ax);
        if r + r2 >= best {
            continue;
        }
        let bx: Vec<u16> = (0..m).map(|i| b[i] ^ x[i]).collect();
        let v = r + r2 + rank_u16(&bx);
        if v < best {
            best = v;
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;

    fn xorshift(s: &mut u64) -> u64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        *s
    }

    #[test]
    fn polynomial_arithmetic() {
        assert_eq!(pmul(0b11, 0b11), 0b101); // (x+1)^2 = x^2+1
        assert_eq!(pdivmod(0b101, 0b11), (0b11, 0));
        let irr = irreducibles(4);
        assert_eq!(irr, vec![0b10, 0b11, 0b111, 0b1011, 0b1101, 0b10011, 0b11001, 0b11111]);
        assert_eq!(factor(0b101), vec![(0b11, 2)]);
        assert_eq!(factor(0b1110), vec![(0b10, 1), (0b111, 1)]);
    }

    #[test]
    fn l_blocks_and_known_pencils() {
        // 3 x L_2 padded to 9x9: rank 9 (every combination has rank 6)
        let mut a = vec![0u16; 9];
        let mut b = vec![0u16; 9];
        for blk in 0..3 {
            let (r0, c0) = (2 * blk, 3 * blk);
            a[r0] |= 1 << c0;
            a[r0 + 1] |= 1 << (c0 + 1);
            b[r0] |= 1 << (c0 + 1);
            b[r0 + 1] |= 1 << (c0 + 2);
        }
        let kr = kronecker(&a, &b, 9, 9);
        assert_eq!(kr.eps, vec![2, 2, 2]);
        assert_eq!(kr.regular_dim, 0);
        // the zero rows/cols: 3 x L_0^T (eta = 0) and... 9 - 6 = 3 zero rows -> 3 L_0^T blocks
        assert_eq!(kr.eta, vec![0, 0, 0]);
        assert_eq!(l_block_rank(1), (2, true));
        assert_eq!(l_block_rank(2), (3, true));
        assert_eq!(l_block_rank(3), (5, true)); // NOT 4 over F_2
        assert_eq!(pencil_rank(&a, &b, 9, 9).0, 9); // 3 * L_2; zero rows add nothing
        assert_eq!(pencil_rank_lb(&a, &b, 9, 9), 9); // s = 3+3+3, excess 0
        // without the zero rows: 6 x 9
        assert_eq!(pencil_rank_lb(&a[..6], &b[..6], 6, 9), 9);
        // regular blocks
        assert_eq!(regular_block_rank(0b111), (3, true)); // x^2+x+1 -> 3
        assert_eq!(regular_block_rank(0b1011), (5, true)); // irreducible cubic -> 5
        assert_eq!(regular_block_rank(0b101), (3, true)); // (x+1)^2 -> 3
        assert_eq!(regular_block_rank(0b110), (2, true)); // x(x+1) -> 2 (diagonalizable)
    }

    fn brute_force_check(sizes: &[(usize, usize)], seed0: u64) {
        let mut seed = seed0;
        let (mut tight, mut add_under, mut add_over, mut total) = (0, 0, 0, 0);
        for &(m, n) in sizes {
            let trials = if m * n >= 25 { 12 } else if m * n >= 12 { 8 } else { 60 };
            for _ in 0..trials {
                let a: Vec<u16> = (0..m).map(|_| (xorshift(&mut seed) as u16) & ((1 << n) - 1)).collect();
                let b: Vec<u16> = (0..m).map(|_| (xorshift(&mut seed) as u16) & ((1 << n) - 1)).collect();
                let bf = pencil_rank_brute(&a, &b, m, n);
                // the Kronecker-side bound (bypassing the whole-pencil brute force)
                let kr = kronecker(&a, &b, m, n);
                let prof = block_profile(&kr);
                let lb: usize = prof.iter().map(|x| x.0).sum::<usize>() + prof.iter().map(|x| x.1).max().unwrap_or(0);
                assert!(lb <= bf, "UNSOUND: pencil {a:?} / {b:?} ({m}x{n}): lb {lb} brute {bf} {kr:?}");
                assert!(pencil_rank_lb(&a, &b, m, n) <= bf);
                let add = pencil_rank_additive(&a, &b, m, n);
                if lb == bf { tight += 1; }
                if add < bf { add_under += 1; }
                if add > bf { add_over += 1; }
                total += 1;
            }
        }
        eprintln!("pencil lb: {tight}/{total} tight; additive sum: {add_under} under, {add_over} OVER (unsound cases) of {total}");
    }

    /// fast sizes (<= 2^16 candidate matrices per pencil): part of the default suite
    #[test]
    fn matches_brute_force_small() {
        brute_force_check(&[(2, 2), (3, 3), (2, 4), (4, 3), (4, 4)], 0x1234_5678_9abc_def1);
    }

    /// 5x5 pencils (2^25 candidates each, 12 trials): minutes in debug —
    /// run with `cargo test --release -- --ignored`
    #[test]
    #[ignore]
    fn matches_brute_force_5x5() {
        brute_force_check(&[(5, 5)], 0x0f0f_1234_5678_9abc);
    }

    #[test]
    fn regular_structured_vs_brute() {
        // (I, A) with chosen invariant structure: direct sums of companion blocks
        let cases: Vec<Vec<u64>> = vec![
            vec![0b101, 0b111],         // (x+1)^2 + (x^2+x+1): 3 + 3 = 6 (D = 4)
            vec![0b100, 0b10],          // x^2 + x: 3 + 1 = 4
            vec![0b1011, 0b11],         // cubic + (x+1): 5 + 1 = 6 (D = 4)
            vec![0b100, 0b100],         // x^2 + x^2 (two invariant factors): 3 + 3 = 6
            vec![0b10011, 0b1],         // irreducible quartic alone
        ];
        for blocks in cases {
            let mut rows: Vec<u16> = Vec::new();
            let mut off = 0usize;
            for &q in &blocks {
                if q == 1 {
                    continue;
                }
                let d = pdeg(q) as usize;
                for r in companion(q) {
                    rows.push(r << off);
                }
                off += d;
            }
            let d = off;
            let mut full = vec![0u16; d];
            let mut o = 0usize;
            for &q in &blocks {
                if q == 1 {
                    continue;
                }
                let dd = pdeg(q) as usize;
                for i in 0..dd {
                    full[o + i] = rows[o + i];
                }
                o += dd;
            }
            let ident: Vec<u16> = (0..d).map(|i| 1u16 << i).collect();
            let (v, _) = pencil_rank(&ident, &full, d, d);
            let expect: usize = blocks.iter().filter(|&&q| q != 1).map(|&q| regular_block_rank(q).0).sum();
            assert_eq!(v, expect, "block decomposition for {blocks:?}");
            if d * d <= 25 {
                let bf = pencil_rank_brute(&ident, &full, d, d);
                let kr = kronecker(&ident, &full, d, d);
                let prof = block_profile(&kr);
                let lb: usize = prof.iter().map(|x| x.0).sum::<usize>() + prof.iter().map(|x| x.1).max().unwrap_or(0);
                assert!(lb <= bf, "UNSOUND lb {lb} > brute {bf} for {blocks:?}");
                eprintln!("blocks {blocks:?}: brute {bf} additive {v} sound-lb {lb}");
            }
        }
    }
}
