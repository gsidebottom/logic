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
//!   G3 (dim 3): planes, see the section below (2026-11-07).
//!
//! Bit matrices: `rows[i]` is row i (a bit of the ROW slot's factor),
//! bit j of it is column j (a bit of the COLUMN slot's factor).  Slots
//! hold at most 25 bits, so u32 rows and at most 32 rows suffice.

use crate::anf::Rng;
use crate::flip::Summand;
use crate::pencil::{pencil_rank_brute, pencil_rank_kron, rank_u16, BRUTE_WHOLE_BITS};
use std::collections::{HashMap, HashSet};
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
    /// G3 plane reductions
    pub g3: AtomicU64,
}

impl GroupStats {
    /// (g1, g2 separate, g2 shared, shuffles, saved, g3)
    pub fn snapshot(&self) -> (u64, u64, u64, u64, u64, u64) {
        (
            self.g1.load(Ordering::Relaxed),
            self.g2_sep.load(Ordering::Relaxed),
            self.g2_shared.load(Ordering::Relaxed),
            self.shuffles.load(Ordering::Relaxed),
            self.saved.load(Ordering::Relaxed),
            self.g3.load(Ordering::Relaxed),
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
pub const SHARED_CAP: usize = 8;

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

// ------------------------------------------------------------------
// G3: planes (dimension 3), 2026-11-07
// ------------------------------------------------------------------
//
// A plane S = span{u, v, w} of one slot's factor space carrying k >= 4
// terms sums to a 3-slice tensor T = sum_c c (x) N_c over the seven
// nonzero codes c in F_2^3 (coordinates in the basis u, v, w), and the
// group may be rewritten with rank(T) terms.
//
// Lower bound (Tomar's coset profiles, arXiv:2610.11823 (3.1), on this
// tiny tensor): a decomposition with n(y) terms of type y satisfies, for
// every nonzero form f on F_2^3, sum_{<f,y>=1} n(y) >= rank(T_f), where
// the slice T_f = sum_{j in f} T_j is the image of T modulo ker f, and
// for every nonzero point x, sum_{y != x} n(y) >= rank of the pencil
// (T_f1, T_f2) with f1, f2 spanning the forms vanishing on x (the image
// of T modulo x), ranked exactly or soundly by pencil.rs.  The least sum
// of a nonnegative integer profile obeying the 14 constraints bounds
// rank(T) from below; if it reaches k the group is proved irreducible.
//
// Upper bound with a witness: the greedy of G2 in each of the 28 bases
// of the dual space: the three pure slices plus shared rank-one matrices
// that lower two or three of them at once (determinant lemma, exact
// candidate sets).  The probe (src/bin/group_probe.rs) closes the gap
// between the two bounds with a SAT call.

/// <f, y> over F_2 for 3-bit codes
#[inline]
fn dot3(f: u32, y: u32) -> u32 {
    (f & y).count_ones() & 1
}

/// element of the plane with basis (u, v, w) at code c (bit 0 = u,
/// bit 1 = v, bit 2 = w)
#[inline]
pub fn plane_elem(basis: &[u32; 3], c: u32) -> u32 {
    let mut x = 0u32;
    for j in 0..3 {
        if c >> j & 1 == 1 {
            x ^= basis[j];
        }
    }
    x
}

/// a plane group: the slot, a basis of the plane (three present
/// factors) and the member terms with their codes in that basis
pub struct PlaneGroup {
    pub t: usize,
    pub basis: [u32; 3],
    pub members: Vec<(usize, u32)>,
}

/// every plane of slot t spanned by three present factors that carries
/// between kmin and kmax terms, each plane once
pub fn plane_groups(s: &[Summand], t: usize, kmin: usize, kmax: usize) -> Vec<PlaneGroup> {
    let mut by: HashMap<u32, Vec<usize>> = HashMap::with_capacity(s.len());
    for (i, m) in s.iter().enumerate() {
        if m[t] != 0 {
            by.entry(m[t]).or_default().push(i);
        }
    }
    let mut vals: Vec<u32> = by.keys().copied().collect();
    vals.sort_unstable();
    let mut seen: HashSet<[u32; 7]> = HashSet::new();
    let mut out = Vec::new();
    for a in 0..vals.len() {
        for b in a + 1..vals.len() {
            let (u, v) = (vals[a], vals[b]);
            for c in b + 1..vals.len() {
                let w = vals[c];
                if w == u ^ v {
                    continue;
                }
                let basis = [u, v, w];
                let mut key = [0u32; 7];
                for code in 1..8u32 {
                    key[(code - 1) as usize] = plane_elem(&basis, code);
                }
                key.sort_unstable();
                if !seen.insert(key) {
                    continue;
                }
                let mut members = Vec::new();
                for code in 1..8u32 {
                    if let Some(idx) = by.get(&plane_elem(&basis, code)) {
                        for &i in idx {
                            members.push((i, code));
                        }
                    }
                }
                if members.len() >= kmin && members.len() <= kmax {
                    out.push(PlaneGroup { t, basis, members });
                }
            }
        }
    }
    out
}

/// the slices of a plane group in the coordinates of its basis: slice j
/// collects the rank-one matrices of the terms whose code has bit j
pub fn plane_slices(s: &[Summand], g: &PlaneGroup, nrows: usize) -> [BitMat; 3] {
    let (o1, o2) = others(g.t);
    let mut sl = [vec![0u32; nrows], vec![0u32; nrows], vec![0u32; nrows]];
    for &(i, code) in &g.members {
        for (j, m) in sl.iter_mut().enumerate() {
            if code >> j & 1 == 1 {
                add_rank1(m, s[i][o1], s[i][o2]);
            }
        }
    }
    sl
}

/// the slice of the form f: XOR of the slices j with bit j of f set
fn form_slice(sl: &[BitMat; 3], f: u32) -> BitMat {
    let n = sl[0].len();
    let mut m = vec![0u32; n];
    for (j, s) in sl.iter().enumerate() {
        if f >> j & 1 == 1 {
            for r in 0..n {
                m[r] ^= s[r];
            }
        }
    }
    m
}

/// a fully reduced echelon basis of the span of some bit vectors; the
/// coordinates of a vector of the span are read off its pivot bits
pub struct Span {
    rows: Vec<(u32, u32)>, // (pivot bit, basis row)
}

impl Span {
    pub fn new(vs: &[u32]) -> Span {
        let mut basis: Vec<(u32, u32)> = Vec::new();
        for &r0 in vs {
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
        Span { rows: basis }
    }
    pub fn dim(&self) -> usize {
        self.rows.len()
    }
    /// coordinates of x (which must lie in the span)
    pub fn coord(&self, x: u32) -> u32 {
        let mut c = 0u32;
        for (j, &(pb, _)) in self.rows.iter().enumerate() {
            if x & pb != 0 {
                c |= 1 << j;
            }
        }
        debug_assert_eq!(self.vector(c), x, "vector outside the span");
        c
    }
    /// the vector with coordinates c
    pub fn vector(&self, c: u32) -> u32 {
        let mut x = 0u32;
        for (j, &(_, br)) in self.rows.iter().enumerate() {
            if c >> j & 1 == 1 {
                x ^= br;
            }
        }
        x
    }
}

/// spans of the row-slot and column-slot factors of a group
pub fn group_spans(s: &[Summand], g: &PlaneGroup) -> (Span, Span) {
    let (o1, o2) = others(g.t);
    let us: Vec<u32> = g.members.iter().map(|&(i, _)| s[i][o1]).collect();
    let vs: Vec<u32> = g.members.iter().map(|&(i, _)| s[i][o2]).collect();
    (Span::new(&us), Span::new(&vs))
}

/// the slices in the coordinates of the two spans (du x dv, u16 rows),
/// for the pencil machinery
pub fn coord_slices(s: &[Summand], g: &PlaneGroup, su: &Span, sv: &Span) -> [Vec<u16>; 3] {
    let (o1, o2) = others(g.t);
    let du = su.dim();
    let mut sl = [vec![0u16; du], vec![0u16; du], vec![0u16; du]];
    for &(i, code) in &g.members {
        let cu = su.coord(s[i][o1]);
        let cv = sv.coord(s[i][o2]) as u16;
        for (j, m) in sl.iter_mut().enumerate() {
            if code >> j & 1 == 1 {
                for r in 0..du {
                    if cu >> r & 1 == 1 {
                        m[r] ^= cv;
                    }
                }
            }
        }
    }
    sl
}

fn compositions(rem: usize, y: usize, n: &mut [usize; 8], ok: &dyn Fn(&[usize; 8]) -> bool) -> bool {
    if y == 7 {
        n[7] = rem;
        return ok(n);
    }
    for v in 0..=rem {
        n[y] = v;
        if compositions(rem - v, y + 1, n, ok) {
            return true;
        }
    }
    n[y] = 0;
    false
}

/// least profile sum in lb0..k meeting the form and point constraints,
/// or k if none does
fn profile_bound(need_f: &[usize; 8], need_x: &[usize; 8], lb0: usize, k: usize) -> usize {
    let feasible = |n: &[usize; 8]| -> bool {
        for f in 1..8u32 {
            let mut tot = 0;
            for y in 1..8u32 {
                if dot3(f, y) == 1 {
                    tot += n[y as usize];
                }
            }
            if tot < need_f[f as usize] {
                return false;
            }
        }
        for x in 1..8usize {
            let tot: usize = (1..8).filter(|&y| y != x).map(|y| n[y]).sum();
            if tot < need_x[x] {
                return false;
            }
        }
        true
    };
    for s in lb0..k {
        let mut n = [0usize; 8];
        if compositions(s, 1, &mut n, &feasible) {
            return s;
        }
    }
    k
}

/// profile lower bound on the rank of the 3-slice tensor given in
/// coordinates (du x dv); returns the least feasible profile sum below
/// k, or k when every profile of sum < k violates a constraint (the
/// group of k terms is then proved irreducible).  Staged from cheap to
/// exact, stopping as soon as a stage closes the group: the seven form
/// ranks alone; then the Kronecker bound on the seven quotient pencils
/// (du, dv <= 9); then, where du * dv <= BRUTE_WHOLE_BITS, their exact
/// brute-force ranks.  Every stage's constraints are sound, so an early
/// stop never weakens a verdict of "closed"; the unstaged bound (brute
/// force on every k = 4 group) cost over 100 ms per group.
pub fn plane_lower_bound(csl: &[Vec<u16>; 3], du: usize, dv: usize, k: usize) -> usize {
    let mut fsl: Vec<Vec<u16>> = vec![vec![0u16; du]; 8];
    for f in 1..8usize {
        for (j, s) in csl.iter().enumerate() {
            if f >> j & 1 == 1 {
                for r in 0..du {
                    fsl[f][r] ^= s[r];
                }
            }
        }
    }
    let mut need_f = [0usize; 8];
    for f in 1..8 {
        need_f[f] = rank_u16(&fsl[f]);
    }
    let lb0 = (1..8).map(|f| need_f[f]).max().unwrap_or(0);
    if lb0 >= k {
        return k;
    }
    let mut need_x = [0usize; 8];
    let b = profile_bound(&need_f, &need_x, lb0, k);
    if b >= k || !((1..=9).contains(&du) && (1..=9).contains(&dv)) {
        return b;
    }
    // two of the three forms vanishing on x span the dual of the quotient by x
    let pair = |x: usize| -> (usize, usize) {
        let fs: Vec<usize> = (1..8usize).filter(|&f| dot3(f as u32, x as u32) == 0).collect();
        (fs[0], fs[1])
    };
    for x in 1..8usize {
        let (f0, f1) = pair(x);
        need_x[x] = pencil_rank_kron(&fsl[f0], &fsl[f1], du, dv);
    }
    let b = profile_bound(&need_f, &need_x, lb0, k);
    if b >= k || du * dv > BRUTE_WHOLE_BITS {
        return b;
    }
    for x in 1..8usize {
        let (f0, f1) = pair(x);
        need_x[x] = need_x[x].max(pencil_rank_brute(&fsl[f0], &fsl[f1], du, dv));
    }
    profile_bound(&need_f, &need_x, lb0, k)
}

/// the rank-one matrices lowering the rank of the matrix with
/// factorization f, as keys (u << 32) | v, sorted; empty above the cap
fn reducer_set(f: &[(u32, u32)], cap: usize) -> Vec<u64> {
    let rho = f.len();
    let mut keys = Vec::new();
    if rho == 0 || rho > cap {
        return keys;
    }
    let mut us = vec![0u32; 1 << rho];
    let mut vs = vec![0u32; 1 << rho];
    for x in 1..(1u32 << rho) {
        let low = x & x.wrapping_neg();
        let j = low.trailing_zeros() as usize;
        us[x as usize] = us[(x ^ low) as usize] ^ f[j].0;
        vs[x as usize] = vs[(x ^ low) as usize] ^ f[j].1;
    }
    for x in 1..(1u32 << rho) {
        for y in 1..(1u32 << rho) {
            if (x & y).count_ones() & 1 == 1 {
                keys.push(((us[x as usize] as u64) << 32) | vs[y as usize] as u64);
            }
        }
    }
    keys.sort_unstable();
    keys.dedup();
    keys
}

/// greedy decomposition of a plane group's tensor in each of the 28
/// bases of the dual space; the cheapest, as (cost, parts), each part a
/// (code in the plane basis, matrix) pair whose factorizations are the
/// new terms
pub fn plane_greedy(sl: &[BitMat; 3], cap: usize) -> (usize, Vec<(u32, BitMat)>) {
    let n = sl[0].len();
    let mut best: Option<(usize, Vec<(u32, BitMat)>)> = None;
    for f1 in 1..8u32 {
        for f2 in f1 + 1..8u32 {
            for f3 in f2 + 1..8u32 {
                if f3 == f1 ^ f2 {
                    continue;
                }
                let fs = [f1, f2, f3];
                // dual basis p_j of the plane: <f_i, p_j> = delta_ij
                let mut p = [0u32; 3];
                for j in 0..3 {
                    p[j] = (1..8u32)
                        .find(|&y| (0..3).all(|i| dot3(fs[i], y) == (i == j) as u32))
                        .expect("dual basis");
                }
                let mut sl3 = [form_slice(sl, f1), form_slice(sl, f2), form_slice(sl, f3)];
                // shared matrices for p0+p1, p0+p2, p1+p2, p0+p1+p2
                let mut shared: [BitMat; 4] =
                    [vec![0u32; n], vec![0u32; n], vec![0u32; n], vec![0u32; n]];
                // candidate sets per slice, rebuilt only for slices that changed
                let mut sets: Vec<Vec<u64>> = vec![Vec::new(), Vec::new(), Vec::new()];
                let mut dirty = [true; 3];
                loop {
                    for j in 0..3 {
                        if dirty[j] {
                            sets[j] = reducer_set(&factorize(&sl3[j]), cap);
                            dirty[j] = false;
                        }
                    }
                    let has = |i: usize, key: u64| sets[i].binary_search(&key).is_ok();
                    let mut pick: Option<(u64, [bool; 3])> = None;
                    // a rank-one lowering all three slices (net gain 2)
                    let i0 = (0..3).min_by_key(|&i| sets[i].len()).unwrap();
                    let (i1, i2) = others(i0);
                    for &key in &sets[i0] {
                        if has(i1, key) && has(i2, key) {
                            pick = Some((key, [true, true, true]));
                            break;
                        }
                    }
                    if pick.is_none() {
                        // a rank-one lowering two slices (net gain 1)
                        'outer: for (a, b) in [(0usize, 1usize), (0, 2), (1, 2)] {
                            let (sm, lg) = if sets[a].len() <= sets[b].len() { (a, b) } else { (b, a) };
                            for &key in &sets[sm] {
                                if has(lg, key) {
                                    let mut w = [false; 3];
                                    w[a] = true;
                                    w[b] = true;
                                    pick = Some((key, w));
                                    break 'outer;
                                }
                            }
                        }
                    }
                    let Some((key, w)) = pick else { break };
                    let (u, v) = ((key >> 32) as u32, key as u32);
                    for j in 0..3 {
                        if w[j] {
                            add_rank1(&mut sl3[j], u, v);
                            dirty[j] = true;
                        }
                    }
                    let si = match w {
                        [true, true, false] => 0,
                        [true, false, true] => 1,
                        [false, true, true] => 2,
                        _ => 3,
                    };
                    add_rank1(&mut shared[si], u, v);
                }
                let cost: usize = sl3.iter().chain(shared.iter()).map(|m| rank(m)).sum();
                if best.as_ref().map(|b| cost < b.0).unwrap_or(true) {
                    let parts = vec![
                        (p[0], sl3[0].clone()),
                        (p[1], sl3[1].clone()),
                        (p[2], sl3[2].clone()),
                        (p[0] ^ p[1], shared[0].clone()),
                        (p[0] ^ p[2], shared[1].clone()),
                        (p[1] ^ p[2], shared[2].clone()),
                        (p[0] ^ p[1] ^ p[2], shared[3].clone()),
                    ];
                    best = Some((cost, parts));
                }
            }
        }
    }
    best.expect("28 bases")
}

/// largest plane group the engine examines (the reducer scans are
/// (2^rho - 1) 2^(rho - 1) candidates per slice of rank rho)
pub const PLANE_KMAX: usize = 8;

/// rank cap for the plane greedy's reducer scans: 8128 candidates per
/// slice at rank 7 (a slice of rank 8 is left without shared candidates)
pub const PLANE_CAP: usize = 7;

/// replace the terms of a plane group by the given parts (codes in the
/// group's basis)
pub fn apply_plane(s: &mut Vec<Summand>, g: &PlaneGroup, parts: &[(u32, BitMat)]) {
    let idx: Vec<usize> = g.members.iter().map(|m| m.0).collect();
    let parts_f: Vec<(u32, BitMat)> =
        parts.iter().map(|(c, m)| (plane_elem(&g.basis, *c), m.clone())).collect();
    apply(s, g.t, &idx, &parts_f, None);
}

/// one plane reduction anywhere in the scheme: a plane group of 4 to
/// PLANE_KMAX terms whose profile bound allows fewer terms and whose
/// greedy decomposition has them.  Returns true and rewrites `s` if so.
pub fn plane_reduce(s: &mut Vec<Summand>, sizes: [usize; 3], st: &GroupStats) -> bool {
    for t in 0..3 {
        let (o1, _) = others(t);
        let groups = plane_groups(s, t, 4, PLANE_KMAX);
        for g in &groups {
            let k = g.members.len();
            let (su, sv) = group_spans(s, g);
            let csl = coord_slices(s, g, &su, &sv);
            if plane_lower_bound(&csl, su.dim(), sv.dim(), k) >= k {
                continue;
            }
            let sl = plane_slices(s, g, sizes[o1]);
            let (cost, parts) = plane_greedy(&sl, PLANE_CAP);
            if cost < k {
                apply_plane(s, g, &parts);
                st.g3.fetch_add(1, Ordering::Relaxed);
                st.saved.fetch_add((k - cost) as u64, Ordering::Relaxed);
                return true;
            }
        }
    }
    false
}

/// the group reductions selected by the move bits: bit 0 = G1 and G2,
/// bit 2 = G3 planes
pub fn group_reduce_m(s: &mut Vec<Summand>, sizes: [usize; 3], st: &GroupStats, moves: u8) -> bool {
    (moves & 1 != 0 && group_reduce(s, sizes, st))
        || (moves & 4 != 0 && plane_reduce(s, sizes, st))
}

#[cfg(test)]
mod plane_tests {
    use super::*;
    use crate::anf::{brent, verify, Dims};
    use crate::flip::{random_flip, summands_to_bits, FlipCfg};

    fn cfg333() -> FlipCfg {
        FlipCfg {
            n1: 3, n2: 3, n3: 3, save_at: 0, record: 0, minutes: 0.0, threads: 1,
            seek_attempts: 100, stall_limit: 8, seed: 1, group_moves: 5, shuffles: 1,
        }
    }

    fn check(s: &[Summand], c: &FlipCfg) {
        let anf = brent(Dims { n1: c.n1, n2: c.n2, n3: c.n3, r: s.len() });
        assert_eq!(verify(&anf, &summands_to_bits(s, c)), 0, "Brent fails at rank {}", s.len());
    }

    /// slices rebuilt from parts must equal the originals
    fn rebuild(parts: &[(u32, BitMat)], n: usize) -> [BitMat; 3] {
        let mut sl = [vec![0u32; n], vec![0u32; n], vec![0u32; n]];
        for (code, m) in parts {
            for j in 0..3 {
                if code >> j & 1 == 1 {
                    for r in 0..n {
                        sl[j][r] ^= m[r];
                    }
                }
            }
        }
        sl
    }

    #[test]
    fn span_coords_roundtrip() {
        let mut rng = Rng::new(9);
        for _ in 0..500 {
            let k = 1 + rng.below(8);
            let vs: Vec<u32> = (0..k).map(|_| (rng.next_u64() as u32) & 0xffff).collect();
            let sp = Span::new(&vs);
            assert_eq!(sp.dim(), rank(&vs));
            for _ in 0..20 {
                let mut x = 0u32;
                for &v in &vs {
                    if rng.f64() < 0.5 {
                        x ^= v;
                    }
                }
                assert_eq!(sp.vector(sp.coord(x)), x);
            }
        }
    }

    #[test]
    fn kronecker_pencil_bound_is_sound_at_small_sizes() {
        let mut rng = Rng::new(23);
        let mut gap = 0usize;
        for _ in 0..400 {
            let m = 1 + rng.below(4);
            let n = 1 + rng.below(4);
            let mask = (1u16 << n) - 1;
            let a: Vec<u16> = (0..m).map(|_| (rng.next_u64() as u16) & mask).collect();
            let b: Vec<u16> = (0..m).map(|_| (rng.next_u64() as u16) & mask).collect();
            let exact = pencil_rank_brute(&a, &b, m, n);
            let kron = pencil_rank_kron(&a, &b, m, n);
            assert!(kron <= exact, "Kronecker bound {kron} above the exact pencil rank {exact} ({m}x{n})");
            gap += exact - kron;
        }
        println!("Kronecker pencil bound vs exact on 400 random pencils (m, n <= 4): total gap {gap}");
    }

    #[test]
    fn plane_bound_below_greedy_and_parts_reproduce() {
        let mut rng = Rng::new(11);
        let mut gap = 0usize;
        for _ in 0..300 {
            let k = 4 + rng.below(5);
            let n = 8;
            // a random plane group: codes include 1, 2, 4 so the basis is present
            let mut terms: Vec<(u32, u32, u32)> = Vec::new();
            for i in 0..k {
                let code = if i < 3 { 1 << i } else { 1 + rng.below(7) as u32 };
                let u = 1 + (rng.next_u64() as u32) % 255;
                let v = 1 + (rng.next_u64() as u32) % 255;
                terms.push((code, u, v));
            }
            let mut sl = [vec![0u32; n], vec![0u32; n], vec![0u32; n]];
            for &(code, u, v) in &terms {
                for j in 0..3 {
                    if code >> j & 1 == 1 {
                        add_rank1(&mut sl[j], u, v);
                    }
                }
            }
            let su = Span::new(&terms.iter().map(|t| t.1).collect::<Vec<_>>());
            let sv = Span::new(&terms.iter().map(|t| t.2).collect::<Vec<_>>());
            let du = su.dim();
            let mut csl = [vec![0u16; du], vec![0u16; du], vec![0u16; du]];
            for &(code, u, v) in &terms {
                let cu = su.coord(u);
                let cv = sv.coord(v) as u16;
                for j in 0..3 {
                    if code >> j & 1 == 1 {
                        for r in 0..du {
                            if cu >> r & 1 == 1 {
                                csl[j][r] ^= cv;
                            }
                        }
                    }
                }
            }
            let lb = plane_lower_bound(&csl, du, sv.dim(), k);
            let (cost, parts) = plane_greedy(&sl, 8);
            assert!(lb <= cost, "bound {lb} above greedy {cost}");
            assert!(lb <= k);
            assert_eq!(rebuild(&parts, n), sl, "parts do not reproduce the slices");
            gap += cost.min(k) - lb.min(cost);
        }
        println!("plane bound vs greedy on 300 random groups: total gap {gap}");
    }

    #[test]
    fn planted_shared_rank_one_is_found() {
        // (1,R1) + (2,R2) + (4,R3) + (3,R) + (4,R) is the 5-term form of
        // the rank-4 tensor (1,R1) + (2,R2) + (4,R3) + (7,R)
        let mut rng = Rng::new(13);
        for _ in 0..200 {
            let n = 8;
            let mut us: Vec<u32> = Vec::new();
            let mut vs: Vec<u32> = Vec::new();
            while us.len() < 4 {
                let u = 1 + (rng.next_u64() as u32) % 255;
                let v = 1 + (rng.next_u64() as u32) % 255;
                if !us.contains(&u) && !vs.contains(&v) {
                    us.push(u);
                    vs.push(v);
                }
            }
            let terms = [(1u32, us[0], vs[0]), (2, us[1], vs[1]), (4, us[2], vs[2]), (3, us[3], vs[3]), (4, us[3], vs[3])];
            let mut sl = [vec![0u32; n], vec![0u32; n], vec![0u32; n]];
            for &(code, u, v) in &terms {
                for j in 0..3 {
                    if code >> j & 1 == 1 {
                        add_rank1(&mut sl[j], u, v);
                    }
                }
            }
            let (cost, parts) = plane_greedy(&sl, 8);
            assert!(cost <= 4, "greedy cost {cost} on a rank-4 tensor written with 5 terms");
            assert_eq!(rebuild(&parts, n), sl);
        }
    }

    #[test]
    fn plane_rewrites_preserve_validity() {
        let c = cfg333();
        let sizes = [9usize, 9, 9];
        let mut rng = Rng::new(17);
        let mut rewritten = 0;
        let mut reduced = 0;
        let st = GroupStats::default();
        for round in 0..6 {
            let mut s: Vec<Summand> = Vec::new();
            for i in 0..3 {
                for k in 0..3 {
                    for j in 0..3 {
                        s.push([1u32 << (i * 3 + k), 1u32 << (k * 3 + j), 1u32 << (i * 3 + j)]);
                    }
                }
            }
            for _ in 0..40 + 24 * round {
                random_flip(&mut s, &mut rng, false);
            }
            check(&s, &c);
            // rewrite the first plane group at its greedy cost, whatever it is
            for t in 0..3 {
                let groups = plane_groups(&s, t, 4, PLANE_KMAX);
                if let Some(g) = groups.first() {
                    let k = g.members.len();
                    let sl = plane_slices(&s, g, sizes[others(t).0]);
                    let (cost, parts) = plane_greedy(&sl, PLANE_CAP);
                    let r0 = s.len();
                    apply_plane(&mut s, g, &parts);
                    check(&s, &c);
                    assert_eq!(s.len(), r0 - k + cost);
                    rewritten += 1;
                    break;
                }
            }
            // and the reducer itself
            let r0 = s.len();
            if plane_reduce(&mut s, sizes, &st) {
                check(&s, &c);
                assert!(s.len() < r0);
                reduced += 1;
            }
        }
        println!("plane rewrites checked: {rewritten}, reductions found by plane_reduce: {reduced}");
        assert!(rewritten > 0, "no plane group met in 6 flipped schemes");
    }
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
