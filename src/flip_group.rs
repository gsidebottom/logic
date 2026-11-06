//! Subspace re-decomposition moves for the mod-2 flip engine (2026-11-06).
//!
//! A scheme is a sum of rank-one terms a (x) b (x) c.  Fix a slot t and a
//! subspace S of that slot's factor space.  The terms whose slot-t factor
//! lies in S sum to a tensor P in S (x) B (x) C, and ANY decomposition of P
//! with slot-t factors in S may replace them: the scheme stays valid by
//! construction.  The flip graph's two moves are the dim-1 cases of this:
//! a flip is a change of basis in the factorization of the terms sharing
//! one factor, a merge is the case where that factorization has fewer terms
//! than the group.  The moves here look one dimension further.
//!
//!   G1 (dim 1): k terms with the same slot-t factor x.  P = x (x) M with
//!       M the sum of the k rank-one matrices b c^T.  If rank M < k the
//!       group is rewritten with rank M terms (a generalized merge: the
//!       classical merge is k = 2, and the case k = 3 with b3 = b1 + b2 and
//!       c3 = c1 + c2, where M = b1 c2^T + b2 c1^T, is invisible to it).
//!   G2 (dim 2): a line {p, q, p+q} carrying k >= 3 terms.  Writing
//!       P = p (x) M_p + q (x) M_q, a decomposition is a choice of the
//!       matrix N attached to the shared element p+q, and it needs
//!       rank(M_p + N) + rank(M_q + N) + rank(N) terms.  Tomar's lifting
//!       criterion (arXiv:2610.11823, Lemma 5.2) is the two-term case
//!       N = 0 up to the choice of basis.  N is built greedily from
//!       rank-one matrices that lower the rank of BOTH slices; each of the
//!       three elements of the line is tried in the shared role.
//!
//! Over F_2 a rank-one matrix lowers the rank of A = C R (full-rank
//! factorization, C with rank A columns) exactly when it is
//! (C x)(R^T y)^T with y^T x = 1 (determinant lemma, I + x y^T singular),
//! so the candidates for N are enumerated exactly, not sampled.
//!
//! Bit matrices: `rows[i]` is row i (a bit of the ROW slot's factor),
//! bit j of it is column j (a bit of the COLUMN slot's factor).  Slots
//! hold at most 25 bits, so u32 rows and at most 32 rows suffice.

use crate::anf::Rng;
use crate::flip::Summand;
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};

/// rows of bits, one u32 per row of the row slot
pub type BitMat = Vec<u32>;

/// counters, shared across worker threads
#[derive(Default)]
pub struct GroupStats {
    /// G1 reductions (same factor, rank M < k)
    pub g1: AtomicU64,
    /// G2 reductions that use only two elements of the line (N = 0)
    pub g2_sep: AtomicU64,
    /// G2 reductions that need the shared element (N != 0)
    pub g2_shared: AtomicU64,
    /// plateau re-decompositions applied at equal rank
    pub shuffles: AtomicU64,
    /// terms removed by all group reductions together
    pub saved: AtomicU64,
}

impl GroupStats {
    pub fn snapshot(&self) -> (u64, u64, u64, u64, u64) {
        (
            self.g1.load(Ordering::Relaxed),
            self.g2_sep.load(Ordering::Relaxed),
            self.g2_shared.load(Ordering::Relaxed),
            self.shuffles.load(Ordering::Relaxed),
            self.saved.load(Ordering::Relaxed),
        )
    }
}

/// the two slots other than t, as (row slot, column slot)
#[inline]
pub fn others(t: usize) -> (usize, usize) {
    match t {
        0 => (1, 2),
        1 => (0, 2),
        _ => (0, 1),
    }
}

#[inline]
pub fn add_rank1(m: &mut [u32], u: u32, v: u32) {
    let mut bits = u;
    while bits != 0 {
        let i = bits.trailing_zeros() as usize;
        m[i] ^= v;
        bits &= bits - 1;
    }
}

/// rank over F_2 (forward elimination on a copy)
pub fn rank(m: &[u32]) -> usize {
    let mut rows: Vec<u32> = m.iter().copied().filter(|&r| r != 0).collect();
    let mut rk = 0;
    for i in 0..rows.len() {
        let piv = rows[i];
        if piv == 0 {
            continue;
        }
        let bit = piv & piv.wrapping_neg();
        rk += 1;
        for j in i + 1..rows.len() {
            if rows[j] & bit != 0 {
                rows[j] ^= piv;
            }
        }
    }
    rk
}

/// full-rank factorization M = sum_j U_j (x) V_j over F_2: the V_j are a
/// reduced echelon basis of the row space, U_j (a bitmask over rows) the
/// coordinates of the rows along V_j.  Exactly rank M pairs, all nonzero.
pub fn factorize(m: &[u32]) -> Vec<(u32, u32)> {
    debug_assert!(m.len() <= 32);
    let mut basis: Vec<(u32, u32)> = Vec::new(); // (pivot bit, row)
    for &r0 in m {
        let mut r = r0;
        for &(pb, br) in &basis {
            if r & pb != 0 {
                r ^= br;
            }
        }
        if r != 0 {
            let pb = r & r.wrapping_neg();
            for (_, br) in basis.iter_mut() {
                if *br & pb != 0 {
                    *br ^= r;
                }
            }
            basis.push((pb, r));
        }
    }
    let mut out: Vec<(u32, u32)> = basis.iter().map(|&(_, br)| (0u32, br)).collect();
    for (i, &r) in m.iter().enumerate() {
        for (j, &(pb, _)) in basis.iter().enumerate() {
            if r & pb != 0 {
                out[j].0 |= 1 << i;
            }
        }
    }
    out
}

/// a factorization with a random change of basis (elementary operations,
/// each of which is itself a flip of the two terms it touches)
pub fn factorize_random(m: &[u32], rng: &mut Rng, ops: usize) -> Vec<(u32, u32)> {
    let mut f = factorize(m);
    let n = f.len();
    if n >= 2 {
        for _ in 0..ops {
            let j = rng.below(n);
            let k = rng.below(n);
            if j == k {
                continue;
            }
            f[j].1 ^= f[k].1; // V_j += V_k
            f[k].0 ^= f[j].0; // U_k += U_j
        }
    }
    f
}

/// enumerate the rank-one matrices u v^T that lower the rank of A (given
/// by its factorization) and ALSO lower the rank of B; returns the first
/// one, or a uniformly random one when `rng` is given.  `cap` bounds the
/// rank of A for which the (2^rho - 1) 2^(rho-1) candidates are scanned.
fn shared_reducer(
    fa: &[(u32, u32)],
    b: &[u32],
    rb: usize,
    cap: usize,
    mut rng: Option<&mut Rng>,
) -> Option<(u32, u32)> {
    let rho = fa.len();
    if rho == 0 || rho > cap || rb == 0 {
        return None;
    }
    let mut pick: Option<(u32, u32)> = None;
    let mut seen = 0u64;
    let mut bb = vec![0u32; b.len()];
    for x in 1u32..(1u32 << rho) {
        let mut u = 0u32;
        for (j, p) in fa.iter().enumerate() {
            if (x >> j) & 1 == 1 {
                u ^= p.0;
            }
        }
        for y in 1u32..(1u32 << rho) {
            if (x & y).count_ones() & 1 == 0 {
                continue;
            }
            let mut v = 0u32;
            for (j, p) in fa.iter().enumerate() {
                if (y >> j) & 1 == 1 {
                    v ^= p.1;
                }
            }
            bb.copy_from_slice(b);
            add_rank1(&mut bb, u, v);
            if rank(&bb) < rb {
                match rng.as_deref_mut() {
                    None => return Some((u, v)),
                    Some(r) => {
                        seen += 1;
                        if r.below(seen as usize) == 0 {
                            pick = Some((u, v));
                        }
                    }
                }
            }
        }
    }
    pick
}

/// greedy shared part for the line decomposition p (x) A + q (x) B:
/// returns (A + N, B + N, N) after adding rank-one matrices that lower
/// both ranks while any exists.
fn shared_greedy(
    mut a: BitMat,
    mut b: BitMat,
    cap: usize,
    mut rng: Option<&mut Rng>,
) -> (BitMat, BitMat, BitMat) {
    let mut n = vec![0u32; a.len()];
    loop {
        let fa = factorize(&a);
        let rb = rank(&b);
        match shared_reducer(&fa, &b, rb, cap, rng.as_deref_mut()) {
            Some((u, v)) => {
                add_rank1(&mut a, u, v);
                add_rank1(&mut b, u, v);
                add_rank1(&mut n, u, v);
            }
            None => break,
        }
    }
    (a, b, n)
}

/// cap on rank A for the exact reducer scan: (2^8 - 1) 2^7 = 32,640
/// candidates at most, each one rank computation.
const SHARED_CAP: usize = 8;

/// the three decompositions of a line group with elements u, v, w = u ^ v
/// and slices (mu, mv) in the basis (u, v): one per choice of the shared
/// element.  Each entry is (cost, [(factor, matrix); 3]).
fn line_options(
    u: u32,
    v: u32,
    mu: &BitMat,
    mv: &BitMat,
    mut rng: Option<&mut Rng>,
) -> Vec<(usize, [(u32, BitMat); 3])> {
    let w = u ^ v;
    let sum: BitMat = mu.iter().zip(mv).map(|(x, y)| x ^ y).collect();
    // (A, B, shared) with factors: A -> fa, B -> fb, N -> fs
    let bases: [(BitMat, BitMat, u32, u32, u32); 3] = [
        (mu.clone(), mv.clone(), u, v, w),   // basis (u, v), shared w
        (sum.clone(), mv.clone(), u, w, v),  // basis (u, w), shared v
        (sum, mu.clone(), v, w, u),          // basis (v, w), shared u
    ];
    let mut out = Vec::with_capacity(3);
    for (a, b, fa, fb, fs) in bases {
        let (a2, b2, n) = shared_greedy(a, b, SHARED_CAP, rng.as_deref_mut());
        let cost = rank(&a2) + rank(&b2) + rank(&n);
        out.push((cost, [(fa, a2), (fb, b2), (fs, n)]));
    }
    out
}

/// replace the terms `idx` by the factorizations of the given
/// (factor, matrix) pairs in slot t
fn apply(
    s: &mut Vec<Summand>,
    t: usize,
    idx: &[usize],
    parts: &[(u32, BitMat)],
    rng: Option<&mut Rng>,
) {
    let (o1, o2) = others(t);
    let mut idx: Vec<usize> = idx.to_vec();
    idx.sort_unstable_by(|a, b| b.cmp(a));
    for i in idx {
        s.swap_remove(i);
    }
    let mut rng = rng;
    for (f, m) in parts {
        let fac = match rng.as_deref_mut() {
            Some(r) => factorize_random(m, r, 6),
            None => factorize(m),
        };
        for (uj, vj) in fac {
            let mut term: Summand = [0; 3];
            term[t] = *f;
            term[o1] = uj;
            term[o2] = vj;
            s.push(term);
        }
    }
}

/// slices of a line group: mu collects the terms with factor u or w,
/// mv those with factor v or w (w = u ^ v contributes to both)
fn line_slices(
    s: &[Summand],
    t: usize,
    nrows: usize,
    iu: &[usize],
    iv: &[usize],
    iw: &[usize],
) -> (BitMat, BitMat) {
    let (o1, o2) = others(t);
    let mut mu = vec![0u32; nrows];
    let mut mv = vec![0u32; nrows];
    for &i in iu {
        add_rank1(&mut mu, s[i][o1], s[i][o2]);
    }
    for &i in iv {
        add_rank1(&mut mv, s[i][o1], s[i][o2]);
    }
    for &i in iw {
        add_rank1(&mut mu, s[i][o1], s[i][o2]);
        add_rank1(&mut mv, s[i][o1], s[i][o2]);
    }
    (mu, mv)
}

/// one group reduction anywhere in the scheme (G1 first, then G2).
/// `sizes` are the bit widths of the three slots.  Returns true and
/// rewrites `s` with fewer terms if a group can be re-decomposed shorter.
pub fn group_reduce(s: &mut Vec<Summand>, sizes: [usize; 3], st: &GroupStats) -> bool {
    // G1: same factor
    for t in 0..3 {
        let (o1, o2) = others(t);
        let nrows = sizes[o1];
        let mut by: HashMap<u32, Vec<usize>> = HashMap::with_capacity(s.len());
        for (i, m) in s.iter().enumerate() {
            by.entry(m[t]).or_default().push(i);
        }
        for (&f, idx) in by.iter() {
            if idx.len() < 2 {
                continue;
            }
            let mut m = vec![0u32; nrows];
            for &i in idx {
                add_rank1(&mut m, s[i][o1], s[i][o2]);
            }
            let rho = rank(&m);
            if rho < idx.len() {
                let k = idx.len();
                apply(s, t, idx, &[(f, m)], None);
                st.g1.fetch_add(1, Ordering::Relaxed);
                st.saved.fetch_add((k - rho) as u64, Ordering::Relaxed);
                return true;
            }
        }
    }
    // G2: lines carrying three distinct factors
    for t in 0..3 {
        let (o1, _) = others(t);
        let nrows = sizes[o1];
        let mut by: HashMap<u32, Vec<usize>> = HashMap::with_capacity(s.len());
        for (i, m) in s.iter().enumerate() {
            by.entry(m[t]).or_default().push(i);
        }
        let mut vals: Vec<u32> = by.keys().copied().collect();
        vals.sort_unstable();
        for a in 0..vals.len() {
            for b in a + 1..vals.len() {
                let (u, v) = (vals[a], vals[b]);
                let w = u ^ v;
                if w <= v {
                    continue; // each line once, from its two smallest elements
                }
                let Some(iw) = by.get(&w) else { continue };
                let (iu, iv) = (&by[&u], &by[&v]);
                let k = iu.len() + iv.len() + iw.len();
                let (mu, mv) = line_slices(s, t, nrows, iu, iv, iw);
                let opts = line_options(u, v, &mu, &mv, None);
                let (cost, parts) = opts
                    .into_iter()
                    .min_by_key(|o| o.0)
                    .unwrap();
                if cost < k {
                    let idx: Vec<usize> =
                        iu.iter().chain(iv).chain(iw).copied().collect();
                    let shared = rank(&parts[2].1) > 0;
                    apply(s, t, &idx, &parts, None);
                    if shared {
                        st.g2_shared.fetch_add(1, Ordering::Relaxed);
                    } else {
                        st.g2_sep.fetch_add(1, Ordering::Relaxed);
                    }
                    st.saved.fetch_add((k - cost) as u64, Ordering::Relaxed);
                    return true;
                }
            }
        }
    }
    false
}

/// plateau move: pick a random line group and rewrite it by a random
/// decomposition of equal (or smaller) cost with randomized
/// factorizations.  Returns true if a rewrite was applied.
pub fn group_shuffle(
    s: &mut Vec<Summand>,
    sizes: [usize; 3],
    rng: &mut Rng,
    st: &GroupStats,
) -> bool {
    // collect line groups over all slots
    let mut groups: Vec<(usize, u32, u32, Vec<usize>, Vec<usize>, Vec<usize>)> = Vec::new();
    for t in 0..3 {
        let mut by: HashMap<u32, Vec<usize>> = HashMap::with_capacity(s.len());
        for (i, m) in s.iter().enumerate() {
            by.entry(m[t]).or_default().push(i);
        }
        let mut vals: Vec<u32> = by.keys().copied().collect();
        vals.sort_unstable();
        for a in 0..vals.len() {
            for b in a + 1..vals.len() {
                let (u, v) = (vals[a], vals[b]);
                let w = u ^ v;
                if w <= v {
                    continue;
                }
                if let Some(iw) = by.get(&w) {
                    groups.push((t, u, v, by[&u].clone(), by[&v].clone(), iw.clone()));
                }
            }
        }
    }
    if groups.is_empty() {
        return false;
    }
    let (t, u, v, iu, iv, iw) = groups.swap_remove(rng.below(groups.len()));
    let (o1, _) = others(t);
    let k = iu.len() + iv.len() + iw.len();
    let (mu, mv) = line_slices(s, t, sizes[o1], &iu, &iv, &iw);
    let mut opts = line_options(u, v, &mu, &mv, Some(rng));
    let best = opts.iter().map(|o| o.0).min().unwrap();
    if best > k {
        return false; // the greedy found nothing as short as the current terms
    }
    // random choice among the options of cost <= k
    opts.retain(|o| o.0 <= k);
    let (cost, parts) = opts.swap_remove(rng.below(opts.len()));
    let idx: Vec<usize> = iu.iter().chain(&iv).chain(&iw).copied().collect();
    apply(s, t, &idx, &parts, Some(rng));
    st.shuffles.fetch_add(1, Ordering::Relaxed);
    if cost < k {
        st.saved.fetch_add((k - cost) as u64, Ordering::Relaxed);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::anf::{brent, verify, Dims};
    use crate::flip::{random_flip, split_toward, summands_to_bits, FlipCfg};
    use crate::pencil::pencil_rank_brute;

    fn cfg(n1: usize, n2: usize, n3: usize) -> FlipCfg {
        FlipCfg {
            n1,
            n2,
            n3,
            save_at: 0,
            record: 0,
            minutes: 0.0,
            threads: 1,
            seek_attempts: 100,
            stall_limit: 8,
            seed: 1,
            group_moves: 3,
            shuffles: 1,
        }
    }

    fn trivial(n1: usize, n2: usize, n3: usize) -> Vec<Summand> {
        let mut s = Vec::new();
        for i in 0..n1 {
            for k in 0..n2 {
                for j in 0..n3 {
                    s.push([
                        1u32 << (i * n2 + k),
                        1u32 << (k * n3 + j),
                        1u32 << (i * n3 + j),
                    ]);
                }
            }
        }
        s
    }

    fn sizes(c: &FlipCfg) -> [usize; 3] {
        [c.n1 * c.n2, c.n2 * c.n3, c.n1 * c.n3]
    }

    fn check(s: &[Summand], c: &FlipCfg) {
        let anf = brent(Dims { n1: c.n1, n2: c.n2, n3: c.n3, r: s.len() });
        assert_eq!(verify(&anf, &summands_to_bits(s, c)), 0, "Brent fails at rank {}", s.len());
    }

    #[test]
    fn factorize_reproduces_matrix() {
        let mut rng = Rng::new(5);
        for _ in 0..2000 {
            let nrows = 1 + rng.below(16);
            let ncols = 1 + rng.below(16);
            let m: Vec<u32> = (0..nrows)
                .map(|_| (rng.next_u64() as u32) & ((1u32 << ncols) - 1) & if rng.f64() < 0.3 { 0 } else { u32::MAX })
                .collect();
            let f = factorize(&m);
            assert_eq!(f.len(), rank(&m));
            let mut back = vec![0u32; nrows];
            for &(u, v) in &f {
                assert!(u != 0 && v != 0);
                add_rank1(&mut back, u, v);
            }
            assert_eq!(back, m);
            let f2 = factorize_random(&m, &mut rng, 5);
            let mut back2 = vec![0u32; nrows];
            for &(u, v) in &f2 {
                add_rank1(&mut back2, u, v);
            }
            assert_eq!(back2, m);
        }
    }

    #[test]
    fn g1_three_terms_to_two() {
        // a (x) b1 (x) c1 + a (x) b2 (x) c2 + a (x) (b1+b2) (x) (c1+c2) has
        // rank 2 in the other slots: invisible to a merge, found by G1
        let c = cfg(3, 3, 3);
        let mut s = trivial(3, 3, 3);
        // build the group from a valid scheme: split one term into three
        // with the pattern above, then re-check validity and reduce back
        let t = s[0];
        let (a, b1, c1) = (t[0], t[1], t[2]);
        let b2 = b1 ^ (1 << 4);
        let c2 = c1 ^ (1 << 5);
        // a(x)b1(x)c1 = a(x)b2(x)c2 + a(x)(b1+b2)(x)(c1+c2) + a(x)b1(x)c1 + ... no:
        // over F2, b1 c1 = b2 c2 + (b1+b2)(c1+c2) + b1 c2 + b2 c1, so use the
        // identity b1 c1 + b2 c2 + (b1+b2)(c1+c2) = b1 c2 + b2 c1 instead:
        // replace a(x)b1(x)c1 by a(x)b1(x)c2 + a(x)b2(x)c1 + a(x)b2(x)c2 + a(x)(b1+b2)(x)(c1+c2)
        s.remove(0);
        s.push([a, b1, c2]);
        s.push([a, b2, c1]);
        s.push([a, b2, c2]);
        s.push([a, b1 ^ b2, c1 ^ c2]);
        check(&s, &c);
        let st = GroupStats::default();
        let r0 = s.len();
        assert!(group_reduce(&mut s, sizes(&c), &st));
        check(&s, &c);
        assert!(s.len() < r0);
        assert_eq!(st.g1.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn moves_preserve_validity() {
        let c = cfg(3, 3, 3);
        let mut s = trivial(3, 3, 3);
        let mut rng = Rng::new(9);
        let st = GroupStats::default();
        let mut reductions = 0;
        for step in 0..30_000 {
            match step % 10 {
                0 if s.len() < 34 => split_toward(&mut s, &mut rng),
                1 => {
                    if group_reduce(&mut s, sizes(&c), &st) {
                        reductions += 1;
                    }
                }
                2 => {
                    group_shuffle(&mut s, sizes(&c), &mut rng, &st);
                }
                _ => {
                    random_flip(&mut s, &mut rng, false);
                }
            }
            if step % 997 == 0 {
                check(&s, &c);
            }
        }
        check(&s, &c);
        assert!(reductions > 0, "no group reduction ever fired");
    }

    #[test]
    fn rectangular_moves_preserve_validity() {
        let c = cfg(3, 3, 4);
        let mut s = trivial(3, 3, 4);
        let mut rng = Rng::new(21);
        let st = GroupStats::default();
        for step in 0..20_000 {
            match step % 10 {
                0 if s.len() < 44 => split_toward(&mut s, &mut rng),
                1 => {
                    group_reduce(&mut s, sizes(&c), &st);
                }
                2 => {
                    group_shuffle(&mut s, sizes(&c), &mut rng, &st);
                }
                _ => {
                    random_flip(&mut s, &mut rng, false);
                }
            }
            if step % 997 == 0 {
                check(&s, &c);
            }
        }
        check(&s, &c);
    }

    #[test]
    fn line_cost_against_exact_pencil_rank() {
        // random 2-slice tensors p (x) A + q (x) B with 4 x 5 slices: the
        // greedy line cost must never beat the exact pencil rank, and we
        // report how often it fails to reach it
        let mut rng = Rng::new(3);
        let (m, n) = (4usize, 4usize);
        let mask = (1u32 << n) - 1;
        let (mut tot, mut gap, mut gapsum) = (0, 0, 0);
        for _ in 0..120 {
            let a: BitMat = (0..m).map(|_| (rng.next_u64() as u32) & mask).collect();
            let b: BitMat = (0..m).map(|_| (rng.next_u64() as u32) & mask).collect();
            let exact = pencil_rank_brute(
                &a.iter().map(|&x| x as u16).collect::<Vec<_>>(),
                &b.iter().map(|&x| x as u16).collect::<Vec<_>>(),
                m,
                n,
            );
            let opts = line_options(1, 2, &a, &b, None);
            let cost = opts.iter().map(|o| o.0).min().unwrap();
            assert!(cost >= exact, "greedy {cost} below exact {exact}");
            // and every option reproduces the tensor
            for (_, parts) in &opts {
                let mut ra = vec![0u32; m];
                let mut rb = vec![0u32; m];
                for (f, mat) in parts {
                    for (u, v) in factorize(mat) {
                        if f & 1 != 0 {
                            add_rank1(&mut ra, u, v);
                        }
                        if f & 2 != 0 {
                            add_rank1(&mut rb, u, v);
                        }
                    }
                }
                assert_eq!(ra, a);
                assert_eq!(rb, b);
            }
            tot += 1;
            if cost > exact {
                gap += 1;
                gapsum += cost - exact;
            }
        }
        eprintln!("line greedy vs exact pencil rank on {tot} random 4x4 pencils: {gap} above exact, total excess {gapsum}");
    }
}
