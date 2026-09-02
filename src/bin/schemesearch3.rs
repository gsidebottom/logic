// CDCL(T) prototype, stage 2: 3x3 scaling probe. Product-level UNSAT ladder
// for <3,3,3> over F_2 with lazy product enumeration (511^3 products — no
// materialized list) and residual-rank theory pruning.
//
// Measurement: the r-ceiling — the largest r whose ladder EXHAUSTS (UNSAT)
// within budget. Every r <= 19 is known UNSAT (Wang's verified certificate:
// rank >= 20), so each rung is a free gate and each exhaustion reproduces
// rank >= r+1 independently. Flattening alone refutes r <= 8 at the root.
//
// Tensor: 729 bits in [u64; 12], bit(a,b,c) = a*81 + b*9 + c, with
// A=(i,j) a=3i+j, B=(j,k) b=3j+k, C=(k,i) c=3k+i (trace convention).
//
// Symmetry (sound, over-counting form): the sandwich group acts on alpha
// through (P,Q) alone, so every scheme has an image in which SOME product's
// alpha is one of the three rank representatives {E11, E11+E22, I}. The
// search enumerates that product first (alpha restricted to the reps, beta
// and gamma free), then the remaining r-1 products over the FULL space in
// strictly decreasing id order, excluding the first. Schemes are enumerated
// at most r times each — redundancy costs time, never completeness. No
// id-order constraint ties the first product to the rest (the stage-1
// unsound-cut lesson).
//
// Propagators: per-node flattening-rank prune (three 9x81 F2 ranks) and an
// optional sound 1-ply substitution probe (--sub-probe): for each side, fold
// the LAST active pivot over its full 2^8 lambda range and take
// 1 + min lambda flatten; depth-gated (--probe-min-remaining) because each
// probe costs ~768 flatten evaluations.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::time::Instant;

const W: usize = 12; // 729 bits
type T3 = [u64; W];

fn bit(a: usize, b: usize, c: usize) -> usize {
    a * 81 + b * 9 + c
}

fn set(t: &mut T3, i: usize) {
    t[i / 64] |= 1u64 << (i % 64);
}

fn get(t: &T3, i: usize) -> bool {
    t[i / 64] >> (i % 64) & 1 == 1
}

fn xor(t: &mut T3, o: &T3) {
    for i in 0..W {
        t[i] ^= o[i];
    }
}

fn is_zero(t: &T3) -> bool {
    t.iter().all(|&w| w == 0)
}

fn build_t3() -> T3 {
    let mut t = [0u64; W];
    for i in 0..3 {
        for j in 0..3 {
            for k in 0..3 {
                set(&mut t, bit(3 * i + j, 3 * j + k, 3 * k + i));
            }
        }
    }
    t
}

fn product_mask(alpha: u32, beta: u32, gamma: u32) -> T3 {
    let mut m = [0u64; W];
    for a in 0..9 {
        if alpha >> a & 1 == 0 {
            continue;
        }
        for b in 0..9 {
            if beta >> b & 1 == 0 {
                continue;
            }
            // gamma occupies 9 consecutive bits at offset a*81 + b*9
            let off = a * 81 + b * 9;
            let (w, s) = (off / 64, off % 64);
            m[w] |= (gamma as u64) << s;
            if s > 55 {
                m[w + 1] |= (gamma as u64) >> (64 - s);
            }
        }
    }
    m
}

/// Leading-bit reduction: maintains <= 9 pivot rows sorted by leading bit,
/// so the work is O(9^2) leading-zero+XOR steps instead of the 81-column
/// Gauss-Jordan scan. Same rank, ~5-9x fewer iterations; the hot kernel
/// under every flatten, probe and ply.
fn rank9_fast(rows: &[u128; 9]) -> u32 {
    let mut piv = [0u128; 9]; // descending by leading bit
    let mut n = 0usize;
    for &r in rows.iter() {
        let mut v = r;
        let mut i = 0usize;
        while v != 0 && i < n {
            let hv = 127 - v.leading_zeros();
            let hp = 127 - piv[i].leading_zeros();
            if hp > hv {
                i += 1;
            } else if hp == hv {
                v ^= piv[i];
                i += 1;
            } else {
                break;
            }
        }
        if v == 0 {
            continue;
        }
        let mut j = n;
        while j > i {
            piv[j] = piv[j - 1];
            j -= 1;
        }
        piv[i] = v;
        n += 1;
    }
    n as u32
}

#[allow(dead_code)]
fn rank9_legacy(rows: &mut [u128; 9]) -> u32 {
    let mut rk = 0usize;
    for c in (0..81).rev() {
        if let Some(p) = (rk..9).find(|&i| rows[i] >> c & 1 == 1) {
            rows.swap(rk, p);
            for i in 0..9 {
                if i != rk && rows[i] >> c & 1 == 1 {
                    rows[i] ^= rows[rk];
                }
            }
            rk += 1;
            if rk == 9 {
                break;
            }
        }
    }
    rk as u32
}

#[inline]
fn extract81(t: &T3, off: usize) -> u128 {
    // 81 bits starting at bit offset `off`: spans at most three words
    let w = off / 64;
    let s = off % 64;
    let mut v = (t[w] as u128) >> s;
    v |= (t[w + 1] as u128) << (64 - s);
    if s > 47 && w + 2 < W {
        v |= (t[w + 2] as u128) << (128 - s);
    }
    v & ((1u128 << 81) - 1)
}

/// Residual in three coordinate layouts: abc (A-major), bca (B-major),
/// cab (C-major). A product mask in a rotated layout is product_mask with
/// rotated arguments, so upkeep is three mask XORs per edge; every
/// flattening is then nine contiguous 81-bit extracts from its layout.
#[derive(Clone, Copy)]
struct R3 {
    abc: T3,
    bca: T3,
    cab: T3,
}

impl R3 {
    fn from_abc(t: &T3) -> R3 {
        let mut r = R3 { abc: *t, bca: [0; W], cab: [0; W] };
        for a in 0..9 {
            for b in 0..9 {
                for c in 0..9 {
                    if get(t, bit(a, b, c)) {
                        set(&mut r.bca, bit(b, c, a));
                        set(&mut r.cab, bit(c, a, b));
                    }
                }
            }
        }
        r
    }
    fn xor_product(&mut self, alpha: u32, beta: u32, gamma: u32) {
        xor(&mut self.abc, &product_mask(alpha, beta, gamma));
        xor(&mut self.bca, &product_mask(beta, gamma, alpha));
        xor(&mut self.cab, &product_mask(gamma, alpha, beta));
    }
    fn is_zero(&self) -> bool {
        is_zero(&self.abc)
    }
}

fn major_rank(t: &T3) -> u32 {
    let mut rows = [0u128; 9];
    for a in 0..9 {
        rows[a] = extract81(t, a * 81);
    }
    rank9_fast(&rows)
}

fn flatten_ranks3(r: &R3) -> [u32; 3] {
    [major_rank(&r.abc), major_rank(&r.bca), major_rank(&r.cab)]
}

fn max_flatten3(r: &R3) -> u32 {
    *flatten_ranks3(r).iter().max().unwrap()
}

// legacy single-layout helpers kept for the probe's fold arithmetic
fn flatten_ranks(t: &T3) -> [u32; 3] {
    let r = R3::from_abc(t);
    flatten_ranks3(&r)
}

fn max_flatten(t: &T3) -> u32 {
    *flatten_ranks(t).iter().max().unwrap()
}

/// whole-array left shift by k bits (k < 729)
fn shl(t: &T3, k: usize) -> T3 {
    let mut out = [0u64; W];
    let (wq, s) = (k / 64, k % 64);
    for i in (wq..W).rev() {
        let mut v = t[i - wq] << s;
        if s > 0 && i > wq {
            v |= t[i - wq - 1] >> (64 - s);
        }
        out[i] = v;
    }
    out
}

fn shr(t: &T3, k: usize) -> T3 {
    let mut out = [0u64; W];
    let (wq, s) = (k / 64, k % 64);
    for i in 0..W - wq {
        let mut v = t[i + wq] >> s;
        if s > 0 && i + wq + 1 < W {
            v |= t[i + wq + 1] << (64 - s);
        }
        out[i] = v;
    }
    out
}

fn and_mask(t: &T3, m: &T3) -> T3 {
    let mut out = *t;
    for i in 0..W {
        out[i] &= m[i];
    }
    out
}

/// Per-layout stride masks: in each layout a side lives at stride 81 (major),
/// 9 (middle) or 1 (minor); MASKS[u][p] selects coordinate p at stride unit
/// u in {81, 9, 1} (index 0/1/2).
struct Masks {
    m: [[T3; 9]; 3],
}

impl Masks {
    fn build() -> Masks {
        let mut m = [[[0u64; W]; 9]; 3];
        for i in 0..729 {
            let (a, b, c) = (i / 81, i / 9 % 9, i % 9);
            set(&mut m[0][a], i);
            set(&mut m[1][b], i);
            set(&mut m[2][c], i);
        }
        Masks { m }
    }
}

/// stride unit of `side` within each layout: layouts abc/bca/cab
/// side A: major in abc (81), minor in bca (1), middle in cab (9)
/// side B: middle in abc (9), major in bca (81), minor in cab (1)
/// side C: minor in abc (1), middle in bca (9), major in cab (81)
const STRIDE_IDX: [[usize; 3]; 3] = [
    // [abc, bca, cab] stride-index (0->81, 1->9, 2->1)
    [0, 2, 1], // side A
    [1, 0, 2], // side B
    [2, 1, 0], // side C
];
const STRIDE_UNIT: [usize; 3] = [81, 9, 1];

fn layout_slice(t: &T3, masks: &Masks, sidx: usize, p: usize) -> T3 {
    and_mask(t, &masks.m[sidx][p])
}

fn layout_shift(m: &T3, sidx: usize, p: usize, q: usize) -> T3 {
    let u = STRIDE_UNIT[sidx];
    if q > p {
        shl(m, (q - p) * u)
    } else {
        shr(m, (p - q) * u)
    }
}

/// Sound 1-ply substitution bound on the triple-layout residual: for each
/// side, take the LAST active pivot and fold it over ALL 2^8 lambdas across
/// all three layouts; rank >= 1 + min over lambda of flatten. Max over sides.
fn sub_bound3(r: &R3, masks: &Masks, best_so_far: u32, target: u32) -> u32 {
    let mut best = best_so_far;
    let layouts = |r: &R3| [r.abc, r.bca, r.cab];
    for side in 0..3usize {
        let sidx = STRIDE_IDX[side];
        // active pivot: nonzero slice in the layout where the side is major
        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
        let lts = layouts(r);
        let p = match (0..9)
            .rev()
            .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
        {
            Some(p) => p,
            None => continue,
        };
        // per-layout base (slice deleted) and per-target shifted slices
        let mut bases = lts;
        let mut slices = [[0u64; W]; 3];
        for l in 0..3 {
            slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
            for i in 0..W {
                bases[l][i] ^= slices[l][i];
            }
        }
        let others: Vec<usize> = (0..9).filter(|&i| i != p).collect();
        let mut shifted: Vec<[T3; 3]> = Vec::with_capacity(8);
        for &q in &others {
            let mut sh = [[0u64; W]; 3];
            for l in 0..3 {
                sh[l] = layout_shift(&slices[l], sidx[l], p, q);
            }
            shifted.push(sh);
        }
        let mut worst = u32::MAX;
        for lam in 0..256u32 {
            let mut m = bases;
            for (bi, sh) in shifted.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    for l in 0..3 {
                        for i in 0..W {
                            m[l][i] ^= sh[l][i];
                        }
                    }
                }
            }
            let f = major_rank(&m[0]).max(major_rank(&m[1])).max(major_rank(&m[2]));
            worst = worst.min(f);
            if 1 + worst <= best {
                break;
            }
        }
        if worst != u32::MAX {
            best = best.max(1 + worst);
        }
        if best >= target {
            return best;
        }
    }
    best
}

// ---- 3c: Koszul flattening propagator (ported from subgame.rs) ----
// Local row-of-bitmask tensor form: t[i][j] = 9-bit mask over k.
struct KT {
    da: usize,
    db: usize,
    dc: usize,
    t: Vec<Vec<u32>>,
}

fn kt_from_abc(t3: &T3) -> KT {
    let mut t = vec![vec![0u32; 9]; 9];
    for a in 0..9 {
        for b in 0..9 {
            let off = a * 81 + b * 9;
            let (w, s) = (off / 64, off % 64);
            let mut chunk = (t3[w] >> s) as u32;
            if s > 55 {
                chunk |= (t3[w + 1] << (64 - s)) as u32;
            }
            t[a][b] = chunk & 0x1FF;
        }
    }
    KT { da: 9, db: 9, dc: 9, t }
}

fn with_side_first(t: &KT, side: u8) -> KT {
    match side {
        1 => KT { da: t.da, db: t.db, dc: t.dc, t: t.t.clone() },
        2 => {
            let mut nt = vec![vec![0u32; t.da]; t.db];
            for i in 0..t.da {
                for j in 0..t.db {
                    nt[j][i] = t.t[i][j];
                }
            }
            KT { da: t.db, db: t.da, dc: t.dc, t: nt }
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
            KT { da: t.dc, db: t.da, dc: t.db, t: nt }
        }
    }
}

/// GE over F2 rows; returns (rank, pivot original-row ids, pivot columns).
/// Origin tracking makes the certifying minor extractable: the original rows
/// selected as pivots I and the pivot columns J satisfy rank(M[I,J]) = rank
/// (the same elimination restricted to I-rows reproduces the pivots).
fn rank_wide_minor(rows: &mut Vec<Vec<u64>>, words: usize) -> (usize, Vec<u32>, Vec<u32>) {
    let n = rows.len();
    let mut orig: Vec<u32> = (0..n as u32).collect();
    let mut rk = 0usize;
    let mut pivot_cols = Vec::new();
    for c in 0..words * 64 {
        let (w, b) = (c / 64, c % 64);
        if let Some(p) = (rk..n).find(|&i| rows[i][w] >> b & 1 == 1) {
            rows.swap(rk, p);
            orig.swap(rk, p);
            for i in 0..n {
                if i != rk && rows[i][w] >> b & 1 == 1 {
                    let (head, tail) = rows.split_at_mut(rk.max(i));
                    if i > rk {
                        for x in 0..words {
                            tail[0][x] ^= head[rk][x];
                        }
                    } else {
                        for x in 0..words {
                            head[i][x] ^= tail[0][x];
                        }
                    }
                }
            }
            pivot_cols.push(c as u32);
            rk += 1;
            if rk == n {
                break;
            }
        }
    }
    (rk, orig[..rk].to_vec(), pivot_cols)
}

/// Forward-only M4R rank over F2: process pivot columns in blocks of k=8;
/// within a block, reduce the k pivot rows against each other so any row's
/// k pivot-column bits directly index a 2^k table of pivot-row combinations
/// (built Gray-code incrementally), clearing all k pivots with ONE row-XOR.
/// ~7x fewer word-ops than the full-Jordan path at koszul sizes; rank-only
/// (the minor-extracting variant keeps the legacy elimination).
fn rank_wide(rows: &mut Vec<Vec<u64>>, words: usize) -> usize {
    const K: usize = 8;
    let n = rows.len();
    let ncols = words * 64;
    let mut rk = 0usize;
    let mut c = 0usize;
    while c < ncols && rk < n {
        // collect up to K pivots starting at column c
        let mut piv_cols: Vec<usize> = Vec::with_capacity(K);
        let block_start = rk;
        while piv_cols.len() < K && c < ncols && rk < n {
            let (w, b) = (c / 64, c % 64);
            let mut found = None;
            for i in rk..n {
                // reduce the candidate against the block's pivots first —
                // an unreduced 1 at column c can be a dependency in disguise
                // (idempotent: earlier-cleared bits stay cleared)
                for (bi, &pc) in piv_cols.iter().enumerate() {
                    let (pw, pb) = (pc / 64, pc % 64);
                    if rows[i][pw] >> pb & 1 == 1 {
                        let (head, tail) = rows.split_at_mut(i);
                        let src = &head[block_start + bi];
                        for x in 0..words {
                            tail[0][x] ^= src[x];
                        }
                    }
                }
                if rows[i][w] >> b & 1 == 1 {
                    found = Some(i);
                    break;
                }
            }
            if let Some(p) = found {
                rows.swap(rk, p);
                // clear this column in the block's other pivot rows only
                for j in block_start..rk {
                    if rows[j][w] >> b & 1 == 1 {
                        let (a, bb) = rows.split_at_mut(rk);
                        for x in 0..words {
                            a[j][x] ^= bb[0][x];
                        }
                    }
                }
                // and clear the new pivot row at earlier block pivot columns
                for (bi, &pc) in piv_cols.iter().enumerate() {
                    let (pw, pb) = (pc / 64, pc % 64);
                    if rows[rk][pw] >> pb & 1 == 1 {
                        let (a, bb) = rows.split_at_mut(rk);
                        for x in 0..words {
                            bb[0][x] ^= a[block_start + bi][x];
                        }
                    }
                }
                piv_cols.push(c);
                rk += 1;
            }
            c += 1;
        }
        let kk = piv_cols.len();
        if kk == 0 {
            continue;
        }
        // Gray-code table of the 2^kk pivot-row combinations
        let mut table = vec![vec![0u64; words]; 1 << kk];
        let mut prev = 0usize;
        for g in 1..(1usize << kk) {
            let gray = g ^ (g >> 1);
            let bit = (gray ^ prev).trailing_zeros() as usize;
            let (dst, src) = (gray, prev);
            let row_src = table[src].clone();
            let piv = rows[block_start + bit].clone();
            let d = &mut table[dst];
            for x in 0..words {
                d[x] = row_src[x] ^ piv[x];
            }
            prev = gray;
        }
        // clear all kk pivots in every remaining row with one XOR
        for i in rk..n {
            let mut idx = 0usize;
            for (bi, &pc) in piv_cols.iter().enumerate() {
                let (w, b) = (pc / 64, pc % 64);
                idx |= ((rows[i][w] >> b & 1) as usize) << bi;
            }
            if idx != 0 {
                let t = &table[idx];
                for x in 0..words {
                    rows[i][x] ^= t[x];
                }
            }
        }
    }
    rk
}

fn rank_wide_legacy(rows: &mut Vec<Vec<u64>>, words: usize) -> usize {
    rank_wide_minor(rows, words).0
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

/// Koszul flattening bound on side A with parameter p (verbatim port of
/// subgame.rs koszul_side; valid over any field, signs vanish over F2).
/// deterministic wedge index tables: sorted masks of popcount p and p+1
fn wedge_indices(da: usize, p: usize) -> (Vec<u32>, Vec<i32>, Vec<u32>, Vec<i32>) {
    let mut masks_p = Vec::new();
    let mut masks_q = Vec::new();
    for m in 0..(1u32 << da) {
        let c = m.count_ones() as usize;
        if c == p {
            masks_p.push(m);
        } else if c == p + 1 {
            masks_q.push(m);
        }
    }
    let mut pos_p = vec![-1i32; 1 << da];
    for (i, &m) in masks_p.iter().enumerate() {
        pos_p[m as usize] = i as i32;
    }
    let mut pos_q = vec![-1i32; 1 << da];
    for (i, &m) in masks_q.iter().enumerate() {
        pos_q[m as usize] = i as i32;
    }
    (masks_p, pos_p, masks_q, pos_q)
}

/// cached wedge tables for da=9, p=1..=7 (index p)
fn wedge_cached(p: usize) -> &'static (Vec<u32>, Vec<i32>, Vec<u32>, Vec<i32>) {
    use std::sync::OnceLock;
    static CACHE: OnceLock<Vec<(Vec<u32>, Vec<i32>, Vec<u32>, Vec<i32>)>> = OnceLock::new();
    &CACHE.get_or_init(|| (0..=7).map(|q| wedge_indices(9, q.max(1))).collect())[p]
}

/// Koszul wedge matrix rows for tensor t (side already rotated to A-first).
fn koszul_rows(t: &KT, p: usize) -> (Vec<Vec<u64>>, usize) {
    let (da, db, dc) = (t.da, t.db, t.dc);
    let cached;
    let computed;
    let (masks_p, _pos_p, pos_q): (&Vec<u32>, &Vec<i32>, &Vec<i32>) = if da == 9 && p <= 7 {
        cached = wedge_cached(p);
        (&cached.0, &cached.1, &cached.3)
    } else {
        computed = wedge_indices(da, p);
        (&computed.0, &computed.1, &computed.3)
    };
    let ncols = masks_p.len() * db;
    let nrows = pos_q.iter().filter(|&&x| x >= 0).count() * dc;
    let words = (ncols + 63) / 64;
    let mut rows = vec![vec![0u64; words]; nrows];
    for (si, &sm) in masks_p.iter().enumerate() {
        for i in 0..da {
            if sm >> i & 1 == 1 {
                continue;
            }
            let qi = pos_q[(sm | (1 << i)) as usize] as usize;
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
    (rows, words)
}

fn koszul_side(t: &KT, p: usize) -> usize {
    let (da, _, _) = (t.da, t.db, t.dc);
    if da < 3 || p == 0 || p + 2 > da {
        return 0;
    }
    let (mut rows, words) = koszul_rows(t, p);
    // Legacy elimination: on the sparse wedge shape it beats M4R 1.5x
    // (measured 2026-08-30) — sparsity short-circuits row-XORs naturally,
    // while M4R pays table + scan-reduction costs regardless.
    let rk = rank_wide_legacy(&mut rows, words);
    let denom = binom(da - 1, p);
    (rk + denom - 1) / denom
}

// NOTE: koszul_rows still allocates per call; buffer reuse measured second-
// order once the wedge tables are cached (allocation is arena-friendly on
// macOS for these sizes). Revisit only if the profile says so.

/// Learned rank certificate: side s, parameter p, pivot columns J of a
/// v-rank minor of K_p(side-rotated R_base). Transfers to residuals R' as
///   bound(R') >= ceil((v - rank(K(Delta)[.,J])) / D),
/// with rank(K(Delta)[.,J]) upper-bounded by the restricted generator span
/// (sound: over-subtracting only weakens the bound).
struct Lemma {
    side: u8,
    p: usize,
    v: usize,
    jcols: Vec<u32>,
    jpos: Vec<i32>, // column id -> position in J, dense (-1 = absent)
}

fn learn_lemma(t: &KT, side: u8, p: usize) -> Option<Lemma> {
    let ts = with_side_first(t, side);
    if ts.da < 3 || p == 0 || p + 2 > ts.da {
        return None;
    }
    let (mut rows, words) = koszul_rows(&ts, p);
    let ncols = words * 64;
    let (v, _i, j) = rank_wide_minor(&mut rows, words);
    let mut jpos = vec![-1i32; ncols];
    for (x, &c) in j.iter().enumerate() {
        jpos[c as usize] = x as i32;
    }
    Some(Lemma { side, p, v, jcols: j, jpos })
}

impl Lemma {
    /// rotated (alpha, beta, gamma) for this lemma's side
    fn rotate(&self, al: u16, be: u16, ga: u16) -> (u16, u16, u16) {
        match self.side {
            1 => (al, be, ga),
            2 => (be, al, ga),
            _ => (ga, al, be),
        }
    }

    /// generators of K(m)[., J] for one product (already side-rotated):
    /// u(S') restricted to J, for S' of popcount p+1 (gamma scaling drops:
    /// rows are u(S') where gamma has a 1, zero otherwise).
    fn gen_rows(&self, al: u16, be: u16, out: &mut Vec<Vec<u64>>, masks_p: &[u32], pos_p: &[i32]) {
        let words = (self.jcols.len() + 63) / 64;
        let da = 9usize;
        for sp in 0..(1u32 << da) {
            if sp.count_ones() as usize != self.p + 1 {
                continue;
            }
            let mut row = vec![0u64; words];
            let mut nz = false;
            for i in 0..da {
                if sp >> i & 1 == 0 || al >> i & 1 == 0 {
                    continue;
                }
                let sm = sp & !(1 << i);
                let si = pos_p[sm as usize];
                if si < 0 {
                    continue;
                }
                for j in 0..9 {
                    if be >> j & 1 == 0 {
                        continue;
                    }
                    let col = si as usize * 9 + j;
                    let x = self.jpos[col];
                    if x >= 0 {
                        row[(x as usize) / 64] |= 1u64 << ((x as usize) % 64);
                        nz = true;
                    }
                }
            }
            if nz {
                out.push(row);
            }
        }
        let _ = masks_p;
    }

    /// transferred bound for residual differing from the base by `delta`
    /// products (side-rotated internally)
    fn bound(&self, delta: &[(u16, u16, u16)], masks_p: &[u32], pos_p: &[i32]) -> u32 {
        let words = (self.jcols.len() + 63) / 64;
        let mut gens: Vec<Vec<u64>> = Vec::new();
        for &(al, be, ga) in delta {
            let (ra, rb, rg) = self.rotate(al, be, ga);
            if rg == 0 {
                continue;
            }
            self.gen_rows(ra, rb, &mut gens, masks_p, pos_p);
        }
        let sub = rank_wide(&mut gens, words);
        let d = binom(8, self.p);
        let v = self.v.saturating_sub(sub);
        ((v + d - 1) / d) as u32
    }
}

/// max Koszul bound over the three sides, p <= pmax
fn koszul_bound3(r: &R3, pmax: usize) -> u32 {
    let kt = kt_from_abc(&r.abc);
    let mut best = 0usize;
    for side in 1..=3u8 {
        let ts = with_side_first(&kt, side);
        for p in 1..=pmax.min(ts.da.saturating_sub(2)) {
            best = best.max(koszul_side(&ts, p));
        }
    }
    best as u32
}

// ---- 3b: GL3(F2) machinery and constructive first-product orbit reps ----
// 3x3 F2 matrices as 9-bit u16 (row-major, row i = bits 3i..3i+2).
fn m3_mul(a: u16, b: u16) -> u16 {
    let mut c = 0u16;
    for i in 0..3 {
        let ar = a >> (3 * i) & 7;
        let mut row = 0u16;
        for j in 0..3 {
            if ar >> j & 1 == 1 {
                row ^= b >> (3 * j) & 7;
            }
        }
        c |= row << (3 * i);
    }
    c
}

fn m3_tr(a: u16) -> u16 {
    let mut t = 0u16;
    for i in 0..3 {
        for j in 0..3 {
            if a >> (3 * i + j) & 1 == 1 {
                t |= 1 << (3 * j + i);
            }
        }
    }
    t
}

const M3_ID: u16 = 0b100_010_001;

fn gl3() -> Vec<u16> {
    let mut out = Vec::with_capacity(168);
    for m in 1u16..512 {
        let (r0, r1, r2) = (m & 7, m >> 3 & 7, m >> 6 & 7);
        if r0 != 0
            && r1 != 0
            && r2 != 0
            && r0 != r1
            && r0 != r2
            && r1 != r2
            && r0 ^ r1 ^ r2 != 0
        {
            out.push(m);
        }
    }
    assert_eq!(out.len(), 168);
    out
}

fn m3_inv(gl: &[u16], a: u16) -> u16 {
    *gl.iter().find(|&&x| m3_mul(a, x) == M3_ID).unwrap()
}

/// Constructive first-product orbit representatives under the sandwich
/// group (P,Q,R): alpha -> P^T alpha Q^T, beta -> Q^-T beta R^T,
/// gamma -> R^-T gamma P^-T (see act_gamma; T-invariance gated in --fold-lemma).
/// Stage A: canonical alpha = min over (P,Q); stage B: beta minimized over
/// Stab(alpha) x R; stage C: gamma minimized over Stab(alpha, beta).
/// Sound by construction: every product is equivalent to a listed rep, and
/// the search's over-counting form needs nothing more.
/// Precomputed stabilizer element: the six matrices needed to act on a
/// product triple: (P^T, Q^T, Q^-T, R^T, P^-1, R^-1).
#[derive(Clone, Copy)]
struct StabElem {
    pt: u16,
    qt: u16,
    qit: u16,
    rt: u16,
    pi: u16,
    ri: u16,
}

impl StabElem {
    fn act(&self, al: u16, be: u16, ga: u16) -> (u16, u16, u16) {
        (
            m3_mul(m3_mul(self.pt, al), self.qt),
            m3_mul(m3_mul(self.qit, be), self.rt),
            act_gamma(self.pi, self.ri, ga),
        )
    }
}

/// C-side action for THIS binary's trace layout (c = 3k+i, i.e. gamma is
/// the (k,i)-indexed matrix): gamma -> R^-T gamma P^-T. subgame.rs uses
/// the (i,k) layout, where the same group element acts as P^-1 gamma R^-1;
/// the two differ by the transpose gamma -> gamma^T. The port carried the
/// (i,k) form verbatim until 2026-09-01, when the --fold-lemma T-invariance
/// gate caught it (the (i,k) form is NOT a symmetry of the (k,i) tensor).
fn act_gamma(pi: u16, ri: u16, ga: u16) -> u16 {
    m3_tr(m3_mul(m3_mul(pi, m3_tr(ga)), ri))
}

fn first_product_reps() -> Vec<(u32, u32, u32, Vec<StabElem>)> {
    let gl = gl3();
    // alpha action table entries: (pt = P^T, qt = Q^T, pinv, rinv-free later)
    // alpha reps: min over all (P,Q)
    let mut alpha_min = [u16::MAX; 512];
    for &p in &gl {
        let pt = m3_tr(p);
        for &q in &gl {
            let qt = m3_tr(q);
            for al in 1u16..512 {
                let im = m3_mul(m3_mul(pt, al), qt);
                if im < alpha_min[al as usize] {
                    alpha_min[al as usize] = im;
                }
            }
        }
    }
    let alpha_reps: Vec<u16> =
        (1u16..512).filter(|&al| alpha_min[al as usize] == al).collect();
    let mut reps = Vec::new();
    for &ar in &alpha_reps {
        // stabilizer pairs (P, Q) with P^T ar Q^T == ar
        let mut stab: Vec<(u16, u16)> = Vec::new();
        for &p in &gl {
            let pt = m3_tr(p);
            for &q in &gl {
                if m3_mul(m3_mul(pt, ar), m3_tr(q)) == ar {
                    stab.push((p, q));
                }
            }
        }
        // beta reps: min over (Q from stab, R free): beta -> Q^-T beta R^T
        let mut beta_min = [u16::MAX; 512];
        for &(_, q) in &stab {
            let qit = m3_tr(m3_inv(&gl, q));
            for &r in &gl {
                let rt = m3_tr(r);
                for be in 1u16..512 {
                    let im = m3_mul(m3_mul(qit, be), rt);
                    if im < beta_min[be as usize] {
                        beta_min[be as usize] = im;
                    }
                }
            }
        }
        let beta_reps: Vec<u16> =
            (1u16..512).filter(|&be| beta_min[be as usize] == be).collect();
        for &br in &beta_reps {
            // stabilizer triples (P, Q, R) fixing (ar, br)
            let mut stab2: Vec<(u16, u16, u16)> = Vec::new();
            for &(p, q) in &stab {
                let qit = m3_tr(m3_inv(&gl, q));
                for &r in &gl {
                    if m3_mul(m3_mul(qit, br), m3_tr(r)) == br {
                        stab2.push((p, q, r));
                    }
                }
            }
            // gamma reps: min over stab2: gamma -> P^-1 gamma R^-1
            let mut gamma_min = [u16::MAX; 512];
            for &(p, _, r) in &stab2 {
                let pi = m3_inv(&gl, p);
                let ri = m3_inv(&gl, r);
                for ga in 1u16..512 {
                    let im = act_gamma(pi, ri, ga);
                    if im < gamma_min[ga as usize] {
                        gamma_min[ga as usize] = im;
                    }
                }
            }
            for ga in 1u16..512 {
                if gamma_min[ga as usize] != ga {
                    continue;
                }
                // full stabilizer of the triple (ar, br, ga)
                let elems: Vec<StabElem> = stab2
                    .iter()
                    .filter_map(|&(p, q, r)| {
                        let pi = m3_inv(&gl, p);
                        let ri = m3_inv(&gl, r);
                        if act_gamma(pi, ri, ga) == ga {
                            Some(StabElem {
                                pt: m3_tr(p),
                                qt: m3_tr(q),
                                qit: m3_tr(m3_inv(&gl, q)),
                                rt: m3_tr(r),
                                pi,
                                ri,
                            })
                        } else {
                            None
                        }
                    })
                    .collect();
                reps.push((ar as u32, br as u32, ga as u32, elems));
            }
        }
    }
    reps
}

// ---- tier-1 oracle ensemble: forced-product and Strassen commutator ----

/// 9x9 F2 matrix as 9 rows of 9 bits
type M9 = [u16; 9];

fn m9_rank(m: &M9) -> u32 {
    let mut rows = *m;
    let mut rk = 0usize;
    for c in (0..9).rev() {
        if let Some(p) = (rk..9).find(|&i| rows[i] >> c & 1 == 1) {
            rows.swap(rk, p);
            for i in 0..9 {
                if i != rk && rows[i] >> c & 1 == 1 {
                    rows[i] ^= rows[rk];
                }
            }
            rk += 1;
        }
    }
    rk as u32
}

fn m9_mul(a: &M9, b: &M9) -> M9 {
    let mut c = [0u16; 9];
    for i in 0..9 {
        let mut row = 0u16;
        for j in 0..9 {
            if a[i] >> j & 1 == 1 {
                row ^= b[j];
            }
        }
        c[i] = row;
    }
    c
}

fn m9_inv(a: &M9) -> Option<M9> {
    let mut m = *a;
    let mut inv: M9 = [0u16; 9];
    for i in 0..9 {
        inv[i] = 1 << i;
    }
    for c in (0..9).rev() {
        let rk = 8 - c;
        let p = (rk..9).find(|&i| m[i] >> c & 1 == 1)?;
        m.swap(rk, p);
        inv.swap(rk, p);
        for i in 0..9 {
            if i != rk && m[i] >> c & 1 == 1 {
                m[i] ^= m[rk];
                inv[i] ^= inv[rk];
            }
        }
    }
    // High-to-low column processing leaves m as the reversal permutation J,
    // so the accumulated ops E satisfy E*A = J and A^-1 = J*E: reverse rows.
    inv.reverse();
    Some(inv)
}

/// slice i of a layout (major axis) as a 9x9 matrix over the two minor axes
fn slice_m9(t: &T3, i: usize) -> M9 {
    let row = extract81(t, i * 81);
    let mut m = [0u16; 9];
    for j in 0..9 {
        m[j] = ((row >> (j * 9)) & 0x1FF) as u16;
    }
    m
}

/// flatten bound of a tensor given as <= 9 slices (81-bit rows, A-major)
fn flatten_of_rows(rows: &[u128]) -> u32 {
    let mut fa = [0u128; 9];
    let mut fb = [0u128; 9];
    let mut fc = [0u128; 9];
    for (a, &r) in rows.iter().enumerate() {
        fa[a] = r;
        for b in 0..9 {
            let chunk = (r >> (b * 9)) & 0x1FF;
            fb[b] |= chunk << (a * 9);
            if chunk != 0 {
                for c in 0..9 {
                    if chunk >> c & 1 == 1 {
                        fc[c] |= 1u128 << (a * 9 + b);
                    }
                }
            }
        }
    }
    rank9_fast(&fa).max(rank9_fast(&fb)).max(rank9_fast(&fc))
}

/// Forced-product bound (Hopcroft-Kerr Lemma 2, Wang's technique ported):
/// per side, independent rank-1 slices become forced products; bound =
/// r1 + min over ALL F2 foldings of the remaining slices' flatten bound.
/// The min must be complete for soundness; widths above the cap return 0.
fn forced_bound3(r: &R3, cap_bits: u32) -> u32 {
    let mut best = 0u32;
    for layout in [&r.abc, &r.bca, &r.cab] {
        let mut r1_rows: Vec<u128> = Vec::new();
        let mut r2p: Vec<u128> = Vec::new();
        for i in 0..9 {
            let row = extract81(layout, i * 81);
            if row == 0 {
                continue;
            }
            let rk = m9_rank(&slice_m9(layout, i));
            if rk == 1 {
                // keep if independent of the chosen r1 rows (GE over 81 bits)
                let mut v = row;
                for &b in &r1_rows {
                    let hb = 127 - b.leading_zeros() as usize;
                    if v >> hb & 1 == 1 {
                        v ^= b;
                    }
                }
                if v != 0 {
                    r1_rows.push(row);
                    continue;
                }
            }
            r2p.push(row);
        }
        let r1 = r1_rows.len() as u32;
        if r1 == 0 {
            continue;
        }
        let width = r1 * r2p.len() as u32;
        if width > cap_bits {
            continue;
        }
        let mut minv = u32::MAX;
        for combo in 0..(1u64 << width) {
            let mut rows: Vec<u128> = r2p.clone();
            for bit in 0..width {
                if combo >> bit & 1 == 1 {
                    let ri = (bit % r1) as usize;
                    let si = (bit / r1) as usize;
                    rows[si] ^= r1_rows[ri];
                }
            }
            minv = minv.min(flatten_of_rows(&rows));
            if minv == 0 {
                break;
            }
        }
        best = best.max(r1 + minv);
    }
    best
}

/// Strassen commutator bound (valid over arbitrary fields; char-2 gated
/// empirically): per side, find an invertible slice-span element S; bound =
/// 9 + ceil(max over slice pairs rank(S1*S2 xor S2*S1) / 2) with
/// Si = S^-1 * slice_i.
fn strassen_bound3(r: &R3, tries: u32) -> u32 {
    let mut best = 0u32;
    let mut seed = 0xabcdef0123456789u64;
    let mut rnd = move || {
        seed ^= seed << 13;
        seed ^= seed >> 7;
        seed ^= seed << 17;
        seed
    };
    for layout in [&r.abc, &r.bca, &r.cab] {
        let slices: Vec<M9> = (0..9).map(|i| slice_m9(layout, i)).collect();
        // find invertible S in the span: individual slices, then random combos
        let mut sinv: Option<M9> = None;
        for s in &slices {
            if let Some(inv) = m9_inv(s) {
                sinv = Some(inv);
                break;
            }
        }
        let mut t = 0;
        while sinv.is_none() && t < tries {
            let mask = (rnd() % 511 + 1) as u16;
            let mut s = [0u16; 9];
            for (i, sl) in slices.iter().enumerate() {
                if mask >> i & 1 == 1 {
                    for j in 0..9 {
                        s[j] ^= sl[j];
                    }
                }
            }
            sinv = m9_inv(&s);
            t += 1;
        }
        let Some(sinv) = sinv else { continue };
        let norm: Vec<M9> = slices.iter().map(|s| m9_mul(&sinv, s)).collect();
        let mut cmax = 0u32;
        for i in 0..9 {
            for j in i + 1..9 {
                let xy = m9_mul(&norm[i], &norm[j]);
                let yx = m9_mul(&norm[j], &norm[i]);
                let mut comm = [0u16; 9];
                for k in 0..9 {
                    comm[k] = xy[k] ^ yx[k];
                }
                cmax = cmax.max(m9_rank(&comm));
            }
        }
        best = best.max(9 + (cmax + 1) / 2);
    }
    best
}

/// Tier 2: 1-ply substitution probe with KOSZUL leaves — bound(R) =
/// 1 + min over (side, last active pivot, all 2^8 lambdas) of
/// koszul(fold(R)). Sound (substitution lemma; folds are restrictions).
/// The target short-circuits the lambda scan; per-eval cost ~ koszul.
fn koszul_probe3(r: &R3, masks: &Masks, pmax: usize, target: u32) -> u32 {
    let mut best = 0u32;
    let layouts = |r: &R3| [r.abc, r.bca, r.cab];
    for side in 0..3usize {
        let sidx = STRIDE_IDX[side];
        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
        let lts = layouts(r);
        let p = match (0..9)
            .rev()
            .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
        {
            Some(p) => p,
            None => continue,
        };
        let mut bases = lts;
        let mut slices = [[0u64; W]; 3];
        for l in 0..3 {
            slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
            for i in 0..W {
                bases[l][i] ^= slices[l][i];
            }
        }
        let others: Vec<usize> = (0..9).filter(|&i| i != p).collect();
        let mut shifted: Vec<[T3; 3]> = Vec::with_capacity(8);
        for &q in &others {
            let mut sh = [[0u64; W]; 3];
            for l in 0..3 {
                sh[l] = layout_shift(&slices[l], sidx[l], p, q);
            }
            shifted.push(sh);
        }
        let mut worst = u32::MAX;
        for lam in 0..256u32 {
            let mut m = bases;
            for (bi, sh) in shifted.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    for l in 0..3 {
                        for i in 0..W {
                            m[l][i] ^= sh[l][i];
                        }
                    }
                }
            }
            let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
            // cheap floor first: flatten, then strassen, then koszul
            let mut f = max_flatten3(&folded).max(strassen_bound3(&folded, 8));
            if f + 1 > worst.saturating_add(1).min(target) {
                // this fold cannot lower the min below current worst; but we
                // still need its koszul only if it could DROP the min
            }
            if f < worst {
                f = f.max(koszul_bound3(&folded, pmax));
            }
            worst = worst.min(f);
            if 1 + worst <= best || 1 + worst < target {
                break; // adversary already spoils the target
            }
        }
        if worst != u32::MAX {
            best = best.max(1 + worst);
        }
        if best >= target {
            return best;
        }
    }
    best
}

/// Item 1 (2026-08-31): killer-directed deep probe. Proves rank(R) >= t by
/// the substitution recursion with lazy evaluation: cheap floors first
/// (flatten 0.2us -> strassen 20us -> koszul ~6ms; leaf if any reaches t),
/// else some (side, last-active-pivot) must have ALL 2^8 folds proving
/// >= t-1. Non-killer folds terminate at their own floor checks; only
/// koszul-dropping folds (the killers) recurse, and recursion targets fall
/// into strassen range within ~2 levels, so depth is self-limiting.
/// Soundness: substitution lemma at every level, sound leaves — the same
/// class as the fixed-ply probes, evaluated adversary-directed.
fn deep_probe(r: &R3, masks: &Masks, t: u32, depth_left: u32) -> bool {
    if max_flatten3(r) >= t {
        return true;
    }
    if t <= 13 && strassen_bound3(r, 8) >= t {
        return true;
    }
    if koszul_bound3(r, 4) >= t {
        return true;
    }
    if depth_left == 0 {
        return false;
    }
    let layouts = |r: &R3| [r.abc, r.bca, r.cab];
    for side in 0..3usize {
        let sidx = STRIDE_IDX[side];
        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
        let lts = layouts(r);
        let p = match (0..9)
            .rev()
            .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
        {
            Some(p) => p,
            None => continue,
        };
        let mut bases = lts;
        let mut slices = [[0u64; W]; 3];
        for l in 0..3 {
            slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
            for w in 0..W {
                bases[l][w] ^= slices[l][w];
            }
        }
        let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
        let shifted: Vec<[T3; 3]> = others
            .iter()
            .map(|&q| {
                let mut sh = [[0u64; W]; 3];
                for l in 0..3 {
                    sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                }
                sh
            })
            .collect();
        let mut all_ok = true;
        for lam in 0..256u32 {
            let mut m = bases;
            for (bi, sh) in shifted.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    for l in 0..3 {
                        for w in 0..W {
                            m[l][w] ^= sh[l][w];
                        }
                    }
                }
            }
            let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
            if !deep_probe(&folded, masks, t - 1, depth_left - 1) {
                all_ok = false;
                break;
            }
        }
        if all_ok {
            return true;
        }
    }
    false
}

/// Parallel deep probe: the top-level fold sweep (the 2^8 lambdas of each
/// side) fans across a thread pool; every fold still runs the SERIAL
/// deep_probe recursion below it. Conjunction semantics with early abort:
/// one failed fold cancels the side. Eliminates the single-threaded tail
/// when slow roots dominate (units-parallel scheduling starves late).
fn deep_probe_par(r: &R3, masks: &Masks, t: u32, depth_left: u32, threads: usize) -> bool {
    if max_flatten3(r) >= t {
        return true;
    }
    if t <= 13 && strassen_bound3(r, 8) >= t {
        return true;
    }
    if koszul_bound3(r, 4) >= t {
        return true;
    }
    if depth_left == 0 {
        return false;
    }
    let layouts = |r: &R3| [r.abc, r.bca, r.cab];
    for side in 0..3usize {
        let sidx = STRIDE_IDX[side];
        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
        let lts = layouts(r);
        let p = match (0..9)
            .rev()
            .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
        {
            Some(p) => p,
            None => continue,
        };
        let mut bases = lts;
        let mut slices = [[0u64; W]; 3];
        for l in 0..3 {
            slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
            for w in 0..W {
                bases[l][w] ^= slices[l][w];
            }
        }
        let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
        let shifted: Vec<[T3; 3]> = others
            .iter()
            .map(|&q| {
                let mut sh = [[0u64; W]; 3];
                for l in 0..3 {
                    sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                }
                sh
            })
            .collect();
        let failed = AtomicBool::new(false);
        let next = AtomicUsize::new(0);
        std::thread::scope(|scope| {
            for _ in 0..threads {
                scope.spawn(|| loop {
                    if failed.load(Ordering::Relaxed) {
                        break;
                    }
                    let lam = next.fetch_add(1, Ordering::Relaxed) as u32;
                    if lam >= 256 {
                        break;
                    }
                    let mut m = bases;
                    for (bi, sh) in shifted.iter().enumerate() {
                        if lam >> bi & 1 == 1 {
                            for l in 0..3 {
                                for w in 0..W {
                                    m[l][w] ^= sh[l][w];
                                }
                            }
                        }
                    }
                    let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
                    if !deep_probe(&folded, masks, t - 1, depth_left - 1) {
                        failed.store(true, Ordering::Relaxed);
                        break;
                    }
                });
            }
        });
        if !failed.load(Ordering::Relaxed) {
            return true;
        }
    }
    false
}

/// Work-queue deep probe (2026-09-01): the same AND-OR tree as deep_probe
/// (OR over sides in order, AND over the 2^8 folds of a side, cheap-floor
/// leaves, depth cap) evaluated by `threads` workers over ONE global task
/// queue: every fold at every depth is a task, so hard folds deep in the
/// recursion no longer serialize a worker (deep_probe_par fans only the
/// top level and idles ~4 of 12 cores on hard roots). Sides stay
/// sequential (side s+1 starts only when side s fails), so the work is
/// the serial tree's work plus early-abort latency. Truth value identical
/// to deep_probe by construction (gate: --probe-pool-test).
struct PoolOr {
    r: R3,
    t: u32,
    depth_left: u32,
    parent: Option<std::sync::Arc<PoolAnd>>,
    resolved: AtomicBool,
    value: AtomicBool,
}

struct PoolAnd {
    parent: std::sync::Arc<PoolOr>,
    side: usize,
    pending: AtomicUsize,
    failed: AtomicBool,
}

struct PoolTask {
    r: R3,
    t: u32,
    depth_left: u32,
    parent: std::sync::Arc<PoolAnd>,
}

struct Pool<'a> {
    masks: &'a Masks,
    queue: std::sync::Mutex<Vec<PoolTask>>,
    cv: std::sync::Condvar,
    done: AtomicBool,
    result: AtomicBool,
    tasks_run: AtomicU64,
    tasks_skipped: AtomicU64,
}

impl<'a> Pool<'a> {
    fn push_side(&self, or: &std::sync::Arc<PoolOr>, from_side: usize) {
        use std::sync::Arc;
        let masks = self.masks;
        let r = &or.r;
        let lts = [r.abc, r.bca, r.cab];
        for side in from_side..3usize {
            let sidx = STRIDE_IDX[side];
            let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
            let p = match (0..9)
                .rev()
                .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
            {
                Some(p) => p,
                None => continue,
            };
            let mut bases = lts;
            let mut slices = [[0u64; W]; 3];
            for l in 0..3 {
                slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
                for w in 0..W {
                    bases[l][w] ^= slices[l][w];
                }
            }
            let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
            let shifted: Vec<[T3; 3]> = others
                .iter()
                .map(|&q| {
                    let mut sh = [[0u64; W]; 3];
                    for l in 0..3 {
                        sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                    }
                    sh
                })
                .collect();
            let and = Arc::new(PoolAnd {
                parent: or.clone(),
                side,
                pending: AtomicUsize::new(256),
                failed: AtomicBool::new(false),
            });
            let mut batch = Vec::with_capacity(256);
            for lam in (0..256u32).rev() {
                let mut m = bases;
                for (bi, sh) in shifted.iter().enumerate() {
                    if lam >> bi & 1 == 1 {
                        for l in 0..3 {
                            for w in 0..W {
                                m[l][w] ^= sh[l][w];
                            }
                        }
                    }
                }
                batch.push(PoolTask {
                    r: R3 { abc: m[0], bca: m[1], cab: m[2] },
                    t: or.t - 1,
                    depth_left: or.depth_left - 1,
                    parent: and.clone(),
                });
            }
            self.queue.lock().unwrap().extend(batch);
            self.cv.notify_all();
            return;
        }
        // no foldable side: the OR fails
        self.or_resolve(or, false);
    }

    fn or_resolve(&self, or: &std::sync::Arc<PoolOr>, value: bool) {
        if or.resolved.swap(true, Ordering::AcqRel) {
            return;
        }
        or.value.store(value, Ordering::Release);
        match &or.parent {
            Some(pand) => {
                if value {
                    self.and_child_ok(pand);
                } else {
                    self.and_child_fail(pand);
                }
            }
            None => {
                self.result.store(value, Ordering::Release);
                self.done.store(true, Ordering::Release);
                let _g = self.queue.lock().unwrap();
                self.cv.notify_all();
            }
        }
    }

    fn and_child_ok(&self, and: &std::sync::Arc<PoolAnd>) {
        if and.failed.load(Ordering::Acquire) {
            return;
        }
        if and.pending.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.or_resolve(&and.parent, true);
        }
    }

    fn and_child_fail(&self, and: &std::sync::Arc<PoolAnd>) {
        if and.failed.swap(true, Ordering::AcqRel) {
            return;
        }
        let or = and.parent.clone();
        self.push_side(&or, and.side + 1);
    }

    /// any ancestor AND already failed or OR already resolved => stale
    fn stale(and: &std::sync::Arc<PoolAnd>) -> bool {
        let mut cur: Option<&std::sync::Arc<PoolAnd>> = Some(and);
        while let Some(a) = cur {
            if a.failed.load(Ordering::Acquire) || a.parent.resolved.load(Ordering::Acquire) {
                return true;
            }
            cur = a.parent.parent.as_ref();
        }
        false
    }

    fn run_task(&self, task: PoolTask) {
        use std::sync::Arc;
        if Self::stale(&task.parent) {
            self.tasks_skipped.fetch_add(1, Ordering::Relaxed);
            return;
        }
        self.tasks_run.fetch_add(1, Ordering::Relaxed);
        let (r, t) = (&task.r, task.t);
        let leaf_ok = max_flatten3(r) >= t
            || (t <= 13 && strassen_bound3(r, 8) >= t)
            || koszul_bound3(r, 4) >= t;
        if leaf_ok {
            self.and_child_ok(&task.parent);
            return;
        }
        if task.depth_left == 0 {
            self.and_child_fail(&task.parent);
            return;
        }
        let or = Arc::new(PoolOr {
            r: task.r,
            t,
            depth_left: task.depth_left,
            parent: Some(task.parent.clone()),
            resolved: AtomicBool::new(false),
            value: AtomicBool::new(false),
        });
        self.push_side(&or, 0);
    }
}

fn deep_probe_pool(r: &R3, masks: &Masks, t: u32, depth_left: u32, threads: usize) -> (bool, u64, u64) {
    use std::sync::Arc;
    if max_flatten3(r) >= t
        || (t <= 13 && strassen_bound3(r, 8) >= t)
        || koszul_bound3(r, 4) >= t
    {
        return (true, 0, 0);
    }
    if depth_left == 0 {
        return (false, 0, 0);
    }
    let pool = Pool {
        masks,
        queue: std::sync::Mutex::new(Vec::new()),
        cv: std::sync::Condvar::new(),
        done: AtomicBool::new(false),
        result: AtomicBool::new(false),
        tasks_run: AtomicU64::new(0),
        tasks_skipped: AtomicU64::new(0),
    };
    let root = Arc::new(PoolOr {
        r: *r,
        t,
        depth_left,
        parent: None,
        resolved: AtomicBool::new(false),
        value: AtomicBool::new(false),
    });
    pool.push_side(&root, 0);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| loop {
                let task = {
                    let mut q = pool.queue.lock().unwrap();
                    loop {
                        if pool.done.load(Ordering::Acquire) {
                            return;
                        }
                        if let Some(t) = q.pop() {
                            break t;
                        }
                        q = pool.cv.wait(q).unwrap();
                    }
                };
                pool.run_task(task);
            });
        }
    });
    (
        pool.result.load(Ordering::Acquire),
        pool.tasks_run.load(Ordering::Relaxed),
        pool.tasks_skipped.load(Ordering::Relaxed),
    )
}

struct Shared {
    capped: AtomicBool,
    found: AtomicBool,
    nodes: AtomicU64,
    prune_flat: AtomicU64,
    prune_sub: AtomicU64,
    prune_koszul: AtomicU64,
    prune_strassen: AtomicU64,
    work: AtomicUsize,
}

struct Search<'a> {
    masks: &'a Masks,
    koszul: usize,             // 0 = off; else max p
    koszul_min_remaining: u32, // apply only at shallow nodes
    stab: &'a [StabElem],      // stabilizer of the current root rep
    strassen: bool,
    deep_probe: u32,
    chosen: Vec<(u32, u32, u32)>,
    level2_remaining: u32,     // remaining value at level-2 nodes (= r-1)
    nodes: u64,
    prune_flat: u64,
    prune_sub: u64,
    prune_koszul: u64,
    prune_strassen: u64,
    sub_probe: bool,
    probe_min_remaining: u32,
    cap: f64,
    start: Instant,
    capped: bool,
    shared: &'a Shared,
}

impl<'a> Search<'a> {
    /// descending lazy iteration over (alpha, beta, gamma), all >= 1,
    /// strictly below `max` (lex on the packed triple), excluding `skip`
    fn dfs(&mut self, r: &R3, remaining: u32, max: u32, skip: u32) -> bool {
        if r.is_zero() {
            return true; // SAT: scheme completed (not expected on this ladder)
        }
        if remaining == 0 {
            return false;
        }
        self.nodes += 1;
        if self.nodes % (1 << 16) == 0 {
            if self.start.elapsed().as_secs_f64() > self.cap {
                self.capped = true;
                self.shared.capped.store(true, Ordering::Relaxed);
            }
            if self.shared.capped.load(Ordering::Relaxed)
                || self.shared.found.load(Ordering::Relaxed)
            {
                self.capped = self.capped || self.shared.capped.load(Ordering::Relaxed);
                return false;
            }
        }
        let fr = max_flatten3(r);
        if fr > remaining {
            self.prune_flat += 1;
            return false;
        }
        // Strassen commutator: strength ~13 at ~20us — the mid-level pruner
        // (bites when remaining <= 13; below 10 flatten handles, above 13 it
        // cannot reach). Gate-validated on constructed-rank tensors.
        if self.strassen && (9..=13).contains(&remaining) {
            if strassen_bound3(r, 8) > remaining {
                self.prune_strassen += 1;
                self.shared.prune_strassen.fetch_add(1, Ordering::Relaxed);
                return false;
            }
        }
        if self.sub_probe && remaining >= self.probe_min_remaining {
            if sub_bound3(r, self.masks, fr, remaining + 1) > remaining {
                self.prune_sub += 1;
                return false;
            }
        }
        if self.koszul > 0 && remaining >= self.koszul_min_remaining {
            if koszul_bound3(r, self.koszul) > remaining {
                self.prune_koszul += 1;
                self.shared.prune_koszul.fetch_add(1, Ordering::Relaxed);
                return false;
            }
        }
        if self.deep_probe > 0 && remaining >= self.koszul_min_remaining {
            if deep_probe(r, self.masks, remaining + 1, self.deep_probe) {
                self.prune_koszul += 1;
                self.shared.prune_koszul.fetch_add(1, Ordering::Relaxed);
                return false;
            }
        }
        let at_level2 = remaining == self.level2_remaining;
        let mut id = max;
        while id > 0 {
            id -= 1;
            let (al, be, ga) = (id >> 18 & 511, id >> 9 & 511, id & 511);
            if al == 0 || be == 0 || ga == 0 {
                // skip ids with a zero component: jump to the next valid id
                if ga == 0 {
                    continue;
                }
                continue;
            }
            if id == skip {
                continue;
            }
            // 4a: at level 2, keep only Stab(root)-orbit-minimal products —
            // sound by the one-deeper normalization (some member of the
            // remaining set is normalizable; levels 3+ stay full-space).
            if at_level2 && !self.stab.is_empty() {
                let (a16, b16, g16) = (al as u16, be as u16, ga as u16);
                let mut minimal = true;
                for e in self.stab {
                    let (ia, ib, ig) = e.act(a16, b16, g16);
                    let iid = (ia as u32) << 18 | (ib as u32) << 9 | ig as u32;
                    if iid < id {
                        minimal = false;
                        break;
                    }
                }
                if !minimal {
                    continue;
                }
            }
            let mut nr = *r;
            nr.xor_product(al, be, ga);
            self.chosen.push((al, be, ga));
            if self.dfs(&nr, remaining - 1, id, skip) {
                return true;
            }
            self.chosen.pop();
            if self.capped {
                return false;
            }
        }
        false
    }
}

/// independent check: rebuild the tensor entrywise from the product triples
fn verify_scheme(products: &[(u32, u32, u32)]) -> bool {
    let t = build_t3();
    for a in 0..9 {
        for b in 0..9 {
            for c in 0..9 {
                let mut bit = 0u32;
                for &(al, be, ga) in products {
                    bit ^= (al >> a) & (be >> b) & (ga >> c) & 1;
                }
                if (bit == 1) != get(&t, a * 81 + b * 9 + c) {
                    return false;
                }
            }
        }
    }
    true
}

fn parse_products(spec: &str) -> Vec<(u32, u32, u32)> {
    spec.split(';')
        .filter(|s| !s.trim().is_empty())
        .map(|p| {
            let v: Vec<u32> = p.split(',').map(|x| x.trim().parse().unwrap()).collect();
            (v[0], v[1], v[2])
        })
        .collect()
}

fn masks_ref(m: &Masks) -> &Masks { m }

fn popcount3(t: &T3) -> u32 {
    t.iter().map(|w| w.count_ones()).sum()
}

/// Greedy-optimal gamma for a fixed (alpha, beta): the product contributes
/// the outer product alpha*beta^T to the c-slice of every c with gamma_c=1,
/// so each c is an independent decision — include it iff it lowers that
/// slice's popcount. Exact optimum of popcount over all 2^9 gammas.
fn best_gamma(r: &R3, alpha: u32, beta: u32) -> (u32, u32) {
    // outer product mask over (a,b) pairs, as a 81-bit map
    let mut ab = [0u16; 9]; // ab[a] = beta if alpha_a else 0
    for a in 0..9 {
        ab[a] = if alpha >> a & 1 == 1 { beta as u16 } else { 0 };
    }
    let mut gamma = 0u32;
    let mut delta: i32 = 0;
    for c in 0..9 {
        // popcount change for slice c
        let mut before = 0i32;
        let mut after = 0i32;
        for a in 0..9 {
            for b in 0..9 {
                let bit = get(&r.abc, bit(a, b, c)) as i32;
                let prod = (ab[a] >> b & 1) as i32;
                before += bit;
                after += bit ^ prod;
            }
        }
        if after < before {
            gamma |= 1 << c;
            delta += after - before;
        }
    }
    (gamma, (-delta) as u32) // gamma and the popcount reduction achieved
}

fn key_dbg(h: &std::sync::Mutex<std::collections::BTreeMap<String, u32>>) -> String {
    format!("{:?}", h.lock().unwrap())
}

/// ply-2 value at a root: 1 + min over folds of koszul_probe3(fold, target-1)
fn ply2_root_t(r3: &R3, masks: &Masks, target: u32) -> u32 {
    let mut best = 0u32;
    let layouts = |r: &R3| [r.abc, r.bca, r.cab];
    for side in 0..3usize {
        let sidx = STRIDE_IDX[side];
        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
        let lts = layouts(r3);
        let p = match (0..9)
            .rev()
            .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
        {
            Some(p) => p,
            None => continue,
        };
        let mut bases = lts;
        let mut slices = [[0u64; W]; 3];
        for l in 0..3 {
            slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
            for w in 0..W {
                bases[l][w] ^= slices[l][w];
            }
        }
        let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
        let shifted: Vec<[T3; 3]> = others
            .iter()
            .map(|&q| {
                let mut sh = [[0u64; W]; 3];
                for l in 0..3 {
                    sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                }
                sh
            })
            .collect();
        let mut worst = u32::MAX;
        for lam in 0..256u32 {
            let mut m = bases;
            for (bi, sh) in shifted.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    for l in 0..3 {
                        for w in 0..W {
                            m[l][w] ^= sh[l][w];
                        }
                    }
                }
            }
            let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
            let pv = koszul_probe3(&folded, masks, 4, target - 1);
            worst = worst.min(pv);
            if 1 + worst < target {
                break;
            }
        }
        if worst != u32::MAX {
            best = best.max(1 + worst);
        }
        if best >= target {
            break;
        }
    }
    best
}

fn ply2_root(r3: &R3, masks: &Masks) -> u32 {
    ply2_root_t(r3, masks, 15)
}

/// ply-3 with a wall-clock budget. Returns None when the budget expires
/// mid-sweep: the min over the adversary's folds is then incomplete, so the
/// value would NOT be a sound lower bound. Only complete sweeps are values.
fn ply3_root_budget(
    r3: &R3,
    masks: &Masks,
    target: u32,
    start: Instant,
    budget_s: f64,
) -> Option<u32> {
    let mut best = 0u32;
    let layouts = |r: &R3| [r.abc, r.bca, r.cab];
    for side in 0..3usize {
        let sidx = STRIDE_IDX[side];
        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
        let lts = layouts(r3);
        let p = match (0..9)
            .rev()
            .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
        {
            Some(p) => p,
            None => continue,
        };
        let mut bases = lts;
        let mut slices = [[0u64; W]; 3];
        for l in 0..3 {
            slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
            for w in 0..W {
                bases[l][w] ^= slices[l][w];
            }
        }
        let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
        let shifted: Vec<[T3; 3]> = others
            .iter()
            .map(|&q| {
                let mut sh = [[0u64; W]; 3];
                for l in 0..3 {
                    sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                }
                sh
            })
            .collect();
        let mut worst = u32::MAX;
        for lam in 0..256u32 {
            if start.elapsed().as_secs_f64() > budget_s {
                return None; // incomplete min: unresolved, not a bound
            }
            let mut m = bases;
            for (bi, sh) in shifted.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    for l in 0..3 {
                        for w in 0..W {
                            m[l][w] ^= sh[l][w];
                        }
                    }
                }
            }
            let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
            let pv = ply2_root_t(&folded, masks, target - 1);
            worst = worst.min(pv);
            if 1 + worst < target {
                break; // adversary spoils the target: complete refutation
            }
        }
        if worst != u32::MAX {
            best = best.max(1 + worst);
        }
        if best >= target {
            break;
        }
    }
    Some(best)
}

#[allow(dead_code)]
fn ply3_root(r3: &R3, masks: &Masks, target: u32) -> u32 {
    let mut best = 0u32;
    let layouts = |r: &R3| [r.abc, r.bca, r.cab];
    for side in 0..3usize {
        let sidx = STRIDE_IDX[side];
        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
        let lts = layouts(r3);
        let p = match (0..9)
            .rev()
            .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks, 0, p)))
        {
            Some(p) => p,
            None => continue,
        };
        let mut bases = lts;
        let mut slices = [[0u64; W]; 3];
        for l in 0..3 {
            slices[l] = layout_slice(&lts[l], masks, sidx[l], p);
            for w in 0..W {
                bases[l][w] ^= slices[l][w];
            }
        }
        let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
        let shifted: Vec<[T3; 3]> = others
            .iter()
            .map(|&q| {
                let mut sh = [[0u64; W]; 3];
                for l in 0..3 {
                    sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                }
                sh
            })
            .collect();
        let mut worst = u32::MAX;
        for lam in 0..256u32 {
            let mut m = bases;
            for (bi, sh) in shifted.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    for l in 0..3 {
                        for w in 0..W {
                            m[l][w] ^= sh[l][w];
                        }
                    }
                }
            }
            let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
            let pv = ply2_root_t(&folded, masks, target - 1);
            worst = worst.min(pv);
            if 1 + worst < target {
                break;
            }
        }
        if worst != u32::MAX {
            best = best.max(1 + worst);
        }
        if best >= target {
            break;
        }
    }
    best
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str| args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned());
    let r: u32 = get("--r").and_then(|v| v.parse().ok()).unwrap_or(9);
    let cap: f64 = get("--time").and_then(|v| v.parse().ok()).unwrap_or(600.0);
    let sub_probe = args.iter().any(|a| a == "--sub-probe");
    let probe_min_remaining: u32 =
        get("--probe-min-remaining").and_then(|v| v.parse().ok()).unwrap_or(3);
    let koszul: usize = get("--koszul").and_then(|v| v.parse().ok()).unwrap_or(0);
    let use_strassen = args.iter().any(|a| a == "--strassen");
    let deep_probe_d: u32 = get("--deep-probe").and_then(|v| v.parse().ok()).unwrap_or(0);
    let koszul_min_remaining: u32 =
        get("--koszul-min-remaining").and_then(|v| v.parse().ok()).unwrap_or(r.saturating_sub(1));

    let t = build_t3();
    assert_eq!(max_flatten(&t), 9, "matmul flattening sanity");

    if args.iter().any(|a| a == "--koszul-depth") {
        // koszul along random product paths: does the 14 persist with depth?
        let mut seed = 0xdeadbeefcafef00du64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for depth in 1..=7usize {
            let mut min_k = u32::MAX;
            let mut sum = 0u32;
            let n = 24;
            for _ in 0..n {
                let mut r3 = R3::from_abc(&build_t3());
                for _ in 0..depth {
                    r3.xor_product(
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                    );
                }
                let k = koszul_bound3(&r3, 4);
                min_k = min_k.min(k);
                sum += k;
            }
            eprintln!("depth {depth}: koszul mean {:.2} min {min_k} (n={n})", sum as f64 / n as f64);
        }
        return;
    }
    if args.iter().any(|a| a == "--oracle-profile") {
        // Strength/cost curves for the tier-1 ensemble on residuals, plus the
        // constructed-rank soundness gate: R = xor of k random products has
        // rank <= k, so any bound > k is UNSOUND.
        let mut seed = 0x5eed5eed5eed5eedu64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        // m9_inv self-test: inverse must verify on random invertible matrices
        {
            let mut sd = 0x1234u64;
            let mut r2 = move || {
                sd ^= sd << 13;
                sd ^= sd >> 7;
                sd ^= sd << 17;
                sd
            };
            let mut tested = 0;
            while tested < 200 {
                let mut m = [0u16; 9];
                for i in 0..9 {
                    m[i] = (r2() % 512) as u16;
                }
                if let Some(inv) = m9_inv(&m) {
                    let prod = m9_mul(&m, &inv);
                    let mut ident = [0u16; 9];
                    for i in 0..9 {
                        ident[i] = 1 << i;
                    }
                    assert_eq!(prod, ident, "m9_inv broken on {:?}", m);
                    tested += 1;
                }
            }
            eprintln!("m9_inv self-test: 200 inverses verified");
        }
        eprintln!("=== soundness gate: constructed rank <= k tensors ===");
        let mut violations = 0u32;
        for k in [5usize, 8, 11, 14, 17] {
            for _ in 0..12 {
                let mut r3 = R3 { abc: [0; W], bca: [0; W], cab: [0; W] };
                for _ in 0..k {
                    r3.xor_product(
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                    );
                }
                let f = max_flatten3(&r3);
                let st = strassen_bound3(&r3, 24);
                let fo = forced_bound3(&r3, 12);
                let kz = koszul_bound3(&r3, 4);
                for (name, v) in [("flat", f), ("strassen", st), ("forced", fo), ("koszul", kz)] {
                    if v as usize > k {
                        eprintln!("  UNSOUND: {name}={v} > k={k}");
                        violations += 1;
                    }
                }
            }
        }
        eprintln!("gate violations: {violations}");
        eprintln!("=== T3 sanity (true rank in [20,23]) ===");
        let t3 = R3::from_abc(&build_t3());
        eprintln!(
            "  flat {} strassen {} forced {} koszul {}",
            max_flatten3(&t3),
            strassen_bound3(&t3, 24),
            forced_bound3(&t3, 12),
            koszul_bound3(&t3, 4)
        );
        eprintln!("=== residual profile (T xor d products), n=24 per depth ===");
        for depth in [1usize, 2, 3, 4, 6] {
            let n = 24;
            let mut stats = [[0u32; 4]; 3]; // [sum, min, fired] x bound — use rows: sum/min/fire
            let mut sums = [0u32; 4];
            let mut mins = [u32::MAX; 4];
            let mut fires = [0u32; 4];
            let mut costs = [0f64; 4];
            for _ in 0..n {
                let mut r3 = R3::from_abc(&build_t3());
                for _ in 0..depth {
                    r3.xor_product(
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                    );
                }
                let evals: [(usize, u32, f64); 4] = {
                    let t0 = Instant::now();
                    let f = max_flatten3(&r3);
                    let c0 = t0.elapsed().as_secs_f64();
                    let t0 = Instant::now();
                    let st = strassen_bound3(&r3, 24);
                    let c1 = t0.elapsed().as_secs_f64();
                    let t0 = Instant::now();
                    let fo = forced_bound3(&r3, 12);
                    let c2 = t0.elapsed().as_secs_f64();
                    let t0 = Instant::now();
                    let kz = koszul_bound3(&r3, 4);
                    let c3 = t0.elapsed().as_secs_f64();
                    [(0, f, c0), (1, st, c1), (2, fo, c2), (3, kz, c3)]
                };
                for (i, v, c) in evals {
                    sums[i] += v;
                    mins[i] = mins[i].min(v);
                    if v > 0 {
                        fires[i] += 1;
                    }
                    costs[i] += c;
                }
                let _ = &mut stats;
            }
            let names = ["flat", "strassen", "forced", "koszul4"];
            let line: Vec<String> = (0..4)
                .map(|i| {
                    format!(
                        "{}: mean {:.1} min {} fire {}/{} {:.2}ms",
                        names[i],
                        sums[i] as f64 / n as f64,
                        if mins[i] == u32::MAX { 0 } else { mins[i] },
                        fires[i],
                        n,
                        costs[i] / n as f64 * 1000.0
                    )
                })
                .collect();
            eprintln!("depth {depth}: {}", line.join(" | "));
        }
        return;
    }
    if args.iter().any(|a| a == "--corridor") {
        // Guided randomized descent toward rank-22 near-misses: choose
        // products minimizing cheap successor bounds; a prefix of length
        // 22-E whose residual bound <= E is a near-miss for the endgame.
        let target: u32 = get("--target").and_then(|v| v.parse().ok()).unwrap_or(22);
        let egame: u32 = get("--endgame-budget").and_then(|v| v.parse().ok()).unwrap_or(7);
        let restarts: u32 = get("--restarts").and_then(|v| v.parse().ok()).unwrap_or(200);
        let cands: u32 = get("--cands").and_then(|v| v.parse().ok()).unwrap_or(2048);
        let mut seed: u64 = get("--seed").and_then(|v| v.parse().ok()).unwrap_or(42);
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let masks = Masks::build();
        let mut best_depth = 0u32;
        let mut near_misses = 0u32;
        for restart in 0..restarts {
            let mut r3 = R3::from_abc(&build_t3());
            let mut prefix: Vec<(u32, u32, u32)> = Vec::new();
            loop {
                let remaining = target - prefix.len() as u32;
                let fb = max_flatten3(&r3);
                if fb > remaining {
                    break; // corridor left
                }
                if remaining <= egame {
                    let pv = sub_bound3(&r3, &masks, fb, remaining + 1);
                    if pv > remaining {
                        break; // probe refutes the handoff: not a real near-miss
                    }
                    near_misses += 1;
                    let spec: Vec<String> =
                        prefix.iter().map(|&(a, b, g)| format!("{a},{b},{g}")).collect();
                    println!("NEARMISS restart {restart} flatten {fb} remaining {remaining}: {}", spec.join(";"));
                    break;
                }
                // Sample (alpha, beta) and complete gamma greedily-optimally;
                // score by residual popcount (flatten is capped at 9 and thus
                // a constant, useless signal until the very end).
                let mut best: Option<(u32, (u32, u32, u32), R3)> = None;
                for _ in 0..cands {
                    let (al, be) = ((rnd() % 511 + 1) as u32, (rnd() % 511 + 1) as u32);
                    let (ga, gain) = best_gamma(&r3, al, be);
                    if ga == 0 || gain == 0 {
                        continue;
                    }
                    let mut nr = r3;
                    nr.xor_product(al, be, ga);
                    if max_flatten3(&nr) > remaining - 1 {
                        continue;
                    }
                    let pc = popcount3(&nr.abc);
                    if best.as_ref().map_or(true, |(bp, _, _)| pc < *bp) {
                        best = Some((pc, (al, be, ga), nr));
                    }
                }
                let Some((_, prod, nr)) = best else { break };
                // probe-gate the step: descend only through states no cheap
                // bound refutes (strassen 20us, then the 1-ply probe 0.36ms)
                let rem_after = remaining - 1;
                if strassen_bound3(&nr, 8) > rem_after {
                    break;
                }
                let fb2 = max_flatten3(&nr);
                if sub_bound3(&nr, &masks, fb2, rem_after + 1) > rem_after {
                    break;
                }
                prefix.push(prod);
                r3 = nr;
                best_depth = best_depth.max(prefix.len() as u32);
            }
        }
        eprintln!("corridor: {restarts} restarts, deepest prefix {best_depth}, near-misses {near_misses}");
        return;
    }
    if let Some(spec) = get("--endgame") {
        // exhaust the remaining budget below a given prefix exactly
        let prefix = parse_products(&spec);
        let egame: u32 = get("--endgame-budget").and_then(|v| v.parse().ok()).unwrap_or(7);
        let mut r3 = R3::from_abc(&build_t3());
        for &(al, be, ga) in &prefix {
            r3.xor_product(al, be, ga);
        }
        let masks = Masks::build();
        let shared = Shared {
            capped: AtomicBool::new(false),
            found: AtomicBool::new(false),
            nodes: AtomicU64::new(0),
            prune_flat: AtomicU64::new(0),
            prune_sub: AtomicU64::new(0),
            prune_koszul: AtomicU64::new(0),
            prune_strassen: AtomicU64::new(0),
            work: AtomicUsize::new(0),
        };
        let cap: f64 = get("--time").and_then(|v| v.parse().ok()).unwrap_or(600.0);
        let mut w = Search {
            masks: &masks,
            koszul: 0,
            koszul_min_remaining: u32::MAX,
            stab: &[],
            strassen: true,
            deep_probe: 0,
            chosen: Vec::new(),
            level2_remaining: u32::MAX,
            nodes: 0,
            prune_flat: 0,
            prune_sub: 0,
            prune_koszul: 0,
            prune_strassen: 0,
            sub_probe: true,
            probe_min_remaining: 3,
            cap,
            start: Instant::now(),
            capped: false,
            shared: &shared,
        };
        let full: u32 = (511 << 18) | (511 << 9) | 511;
        let found = w.dfs(&r3, egame, full + 1, 0);
        if found {
            let mut scheme = prefix.clone();
            scheme.extend(w.chosen.iter());
            let ok = verify_scheme(&scheme);
            println!(
                "ENDGAME SAT — {} products, independent verify {}",
                scheme.len(),
                if ok { "OK" } else { "FAILED" }
            );
            for (i, (a, b, g)) in scheme.iter().enumerate() {
                println!("  p{}: {a},{b},{g}", i + 1);
            }
            assert!(ok);
        } else if w.capped {
            println!("ENDGAME CAP ({} nodes)", w.nodes);
        } else {
            println!("ENDGAME UNSAT ({} nodes) — prefix refuted", w.nodes);
        }
        return;
    }
    if args.iter().any(|a| a == "--wedge-correlate") {
        // The alignment correlate: for sampled roots and every fold phi
        // (side A, pivot 8), compute on the p=4 side-A wedge:
        //   v_T = rank K(T|ker phi),  b = rank K(m1|ker phi),
        //   d = dim(rowspace K(m1|phi) ∩ rowspace K(T|phi))
        //     = v_T + b - rank(stacked),
        //   drop = v_T - v_R  (R = T xor m1)
        // and correlate with killer status (full koszul_bound3 < 14).
        let reps = first_product_reps();
        let masks = Masks::build();
        let t3 = R3::from_abc(&build_t3());
        let sample: Vec<usize> = vec![0, 1, 4, 10, 25, 58, 92, 143];
        fn rank3m(bits9: u32) -> u32 {
            let mut rows = [bits9 & 7, bits9 >> 3 & 7, bits9 >> 6 & 7];
            let mut rk = 0usize;
            for c in (0..3).rev() {
                if let Some(p) = (rk..3).find(|&i| rows[i] >> c & 1 == 1) {
                    rows.swap(rk, p);
                    for i in 0..3 {
                        if i != rk && rows[i] >> c & 1 == 1 {
                            rows[i] ^= rows[rk];
                        }
                    }
                    rk += 1;
                }
            }
            rk as u32
        }
        let fold_r3 = |r: &R3, lam: u32| -> R3 {
            let p = 8usize;
            let sidx = STRIDE_IDX[0];
            let lts = [r.abc, r.bca, r.cab];
            let mut bases = lts;
            let mut slices = [[0u64; W]; 3];
            for l in 0..3 {
                slices[l] = layout_slice(&lts[l], &masks, sidx[l], p);
                for w in 0..W {
                    bases[l][w] ^= slices[l][w];
                }
            }
            let others: Vec<usize> = (0..8).collect();
            for (bi, &q) in others.iter().enumerate() {
                if lam >> bi & 1 == 1 {
                    for l in 0..3 {
                        let sh = layout_shift(&slices[l], sidx[l], p, q);
                        for w in 0..W {
                            bases[l][w] ^= sh[w];
                        }
                    }
                }
            }
            R3 { abc: bases[0], bca: bases[1], cab: bases[2] }
        };
        let wedge_rank = |r3: &R3| -> (usize, Vec<Vec<u64>>, usize) {
            let kt = kt_from_abc(&r3.abc);
            let (rows, words) = koszul_rows(&kt, 4);
            let mut rr = rows.clone();
            let rk = rank_wide_legacy(&mut rr, words);
            (rk, rows, words)
        };
        // per (rank_phi, killer): distributions of d and drop
        use std::collections::BTreeMap;
        let mut agg: BTreeMap<(u32, bool), BTreeMap<(usize, usize), u32>> = BTreeMap::new();
        for &ri in &sample {
            let (al, be, ga, _) = reps[ri];
            let mut m1 = R3 { abc: [0; W], bca: [0; W], cab: [0; W] };
            m1.xor_product(al, be, ga);
            let mut rr3 = t3;
            rr3.xor_product(al, be, ga);
            for lam in 0..256u32 {
                let phi_rank = rank3m((1 << 8) | lam);
                let tf = fold_r3(&t3, lam);
                let mf = fold_r3(&m1, lam);
                let rf = fold_r3(&rr3, lam);
                let (v_t, rows_t, words) = wedge_rank(&tf);
                let (b, rows_m, _) = wedge_rank(&mf);
                let (v_r, _, _) = wedge_rank(&rf);
                let mut stacked = rows_t.clone();
                stacked.extend(rows_m.iter().cloned());
                let v_stack = rank_wide_legacy(&mut stacked, words);
                let d = v_t + b - v_stack;
                let drop = v_t.saturating_sub(v_r);
                let killer = koszul_bound3(&rf, 4) < 14;
                if (phi_rank == 2 && killer) || (lam % 61 == 0) {
                    println!(
                        "  root {ri} lam {lam:3} rankphi {phi_rank} killer {killer}: v_T {v_t} b {b} d {d} contain {} drop {drop} v_R {v_r}",
                        d == b
                    );
                }
                *agg.entry((phi_rank, killer)).or_default().entry((d, drop)).or_insert(0) += 1;
            }
            eprintln!("root {ri} done");
        }
        println!("(rank_phi, killer) -> {{(intersection d, wedge drop): count}}");
        for (k, v) in &agg {
            // summarize: d range and drop range
            let dmin = v.keys().map(|x| x.0).min().unwrap();
            let dmax = v.keys().map(|x| x.0).max().unwrap();
            let drmin = v.keys().map(|x| x.1).min().unwrap();
            let drmax = v.keys().map(|x| x.1).max().unwrap();
            let n: u32 = v.values().sum();
            println!("  {k:?}: n={n} d in [{dmin},{dmax}] drop in [{drmin},{drmax}]");
        }
        return;
    }
    if args.iter().any(|a| a == "--orbit-audit") {
        // Coverage audit of the pre-fix 211 roots (rep triples read from
        // matmul/r22/killers.txt) against the TRUE first-product orbits:
        // each old root is canonicalized under the correct action and the
        // set of true orbits it hits is counted.
        let reps = first_product_reps();
        let gl = gl3();
        let mut inv = [0u16; 512];
        for &p in &gl {
            inv[p as usize] = m3_inv(&gl, p);
        }
        let rep_set: std::collections::HashSet<(u16, u16, u16)> =
            reps.iter().map(|&(a, b, g, _)| (a as u16, b as u16, g as u16)).collect();
        println!("true first-product orbits: {}", reps.len());
        let mut old: Vec<(u16, u16, u16)> = Vec::new();
        for line in std::fs::read_to_string("matmul/r22/killers.txt").unwrap().lines() {
            let f: Vec<&str> = line.split_whitespace().collect();
            if f.len() > 3 && f[2] == "rep" {
                let v: Vec<u16> = f[3].split(',').map(|x| x.parse().unwrap()).collect();
                let t = (v[0], v[1], v[2]);
                if !old.contains(&t) {
                    old.push(t);
                }
            }
        }
        println!("old roots: {}", old.len());
        let canon = |al: u16, be: u16, ga: u16| -> (u16, u16, u16) {
            let mut amin = u16::MAX;
            let mut g1: Vec<(u16, u16)> = Vec::new();
            for &p in &gl {
                for &q in &gl {
                    let im = m3_mul(m3_mul(m3_tr(p), al), m3_tr(q));
                    if im < amin {
                        amin = im;
                        g1.clear();
                    }
                    if im == amin {
                        g1.push((p, q));
                    }
                }
            }
            let mut bmin = u16::MAX;
            let mut g2: Vec<(u16, u16, u16)> = Vec::new();
            for &(p, q) in &g1 {
                let qit = m3_tr(inv[q as usize]);
                for &r in &gl {
                    let im = m3_mul(m3_mul(qit, be), m3_tr(r));
                    if im < bmin {
                        bmin = im;
                        g2.clear();
                    }
                    if im == bmin {
                        g2.push((p, q, r));
                    }
                }
            }
            let gmin = g2
                .iter()
                .map(|&(p, _, r)| act_gamma(inv[p as usize], inv[r as usize], ga))
                .min()
                .unwrap();
            (amin, bmin, gmin)
        };
        let mut covered: std::collections::HashSet<(u16, u16, u16)> = Default::default();
        let mut ab_changed = 0;
        for &(al, be, ga) in &old {
            let c = canon(al, be, ga);
            assert!(rep_set.contains(&c), "canonical form {c:?} of old root {:?} missing from reps", (al, be, ga));
            if (c.0, c.1) != (al, be) {
                ab_changed += 1;
            }
            covered.insert(c);
        }
        println!(
            "old roots cover {} of {} true orbits ({} old roots had a non-canonical (alpha,beta))",
            covered.len(),
            reps.len(),
            ab_changed
        );
        let missing: Vec<(u16, u16, u16)> = reps
            .iter()
            .map(|&(a, b, g, _)| (a as u16, b as u16, g as u16))
            .filter(|t| !covered.contains(t))
            .collect();
        println!("uncovered true orbits: {}", missing.len());
        for t in &missing {
            println!("  uncovered {},{},{}", t.0, t.1, t.2);
        }
        return;
    }
    if args.iter().any(|a| a == "--fold-lemma") {
        // THE CASE-SPLIT LEMMA by orbit exhaustion (2026-09-01).
        // For every rank-one m = al x be x ga (511^3) and every fold
        // vector v in A (511), the side-A Koszul data of (T + m) folded
        // by v is a sandwich invariant of the pair (m, v). The sandwich
        // group is transitive on the rank classes of v, so WLOG v is a
        // class rep (E33 / E22+E33 / I, all with the probe's pivot 8);
        // the orbits of m under Stab(v) x GL3(R) are enumerated exactly
        // by a staged lex-min canonical form, and the orbit sizes must
        // sum to 511^3 (completeness gate). Every orbit is evaluated:
        // embedded p=4 wedge rank e4 (the probe's quantity, threshold
        // 911 for koszul 14), the honest 8-dim ranks h3, h4 on A/v
        // (e4 == h3 + h4, asserted), and the full koszul_bound3.
        // Transport: every (root, side, lambda) of the killer-dump is
        // mapped to its rep and the table value is compared with the
        // direct computation (value-by-value gate against the dump).
        let masks = Masks::build();
        let t3 = R3::from_abc(&build_t3());
        assert_eq!(t3.bca, t3.abc, "T cyclic invariance");
        assert_eq!(t3.cab, t3.abc, "T cyclic invariance");
        let gl = gl3();
        let mut inv = [0u16; 512];
        for &p in &gl {
            inv[p as usize] = m3_inv(&gl, p);
        }
        let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
        let ranks: Vec<u32> = get("--fold-rank")
            .map(|v| v.split(',').map(|x| x.parse().unwrap()).collect())
            .unwrap_or(vec![3, 2, 1]);
        fn rank3m(bits9: u32) -> u32 {
            let mut rows = [bits9 & 7, bits9 >> 3 & 7, bits9 >> 6 & 7];
            let mut rk = 0usize;
            for c in (0..3).rev() {
                if let Some(p) = (rk..3).find(|&i| rows[i] >> c & 1 == 1) {
                    rows.swap(rk, p);
                    for i in 0..3 {
                        if i != rk && rows[i] >> c & 1 == 1 {
                            rows[i] ^= rows[rk];
                        }
                    }
                    rk += 1;
                }
            }
            rk as u32
        }
        let mk = |p: u16, q: u16, r: u16| StabElem {
            pt: m3_tr(p),
            qt: m3_tr(q),
            qit: m3_tr(inv[q as usize]),
            rt: m3_tr(r),
            pi: inv[p as usize],
            ri: inv[r as usize],
        };
        let act_v = |e: &StabElem, v: u16| m3_mul(m3_mul(e.pt, v), e.qt);
        // side-A fold by v: pivot = leading set bit, lambda = the rest
        // (hyperplane-koszul convention; == the probe for v_8 = 1).
        let fold_v = |r: &R3, v: u32| -> R3 {
            let p = (31 - v.leading_zeros()) as usize;
            let sidx = STRIDE_IDX[0];
            let lts = [r.abc, r.bca, r.cab];
            let mut bases = lts;
            let mut slices = [[0u64; W]; 3];
            for l in 0..3 {
                slices[l] = layout_slice(&lts[l], &masks, sidx[l], p);
                for w in 0..W {
                    bases[l][w] ^= slices[l][w];
                }
            }
            for q in 0..9 {
                if q != p && v >> q & 1 == 1 {
                    for l in 0..3 {
                        let sh = layout_shift(&slices[l], sidx[l], p, q);
                        for w in 0..W {
                            bases[l][w] ^= sh[w];
                        }
                    }
                }
            }
            R3 { abc: bases[0], bca: bases[1], cab: bases[2] }
        };
        // (embedded p=4 rank, honest r3, honest r4 on the 8-dim A/v)
        let wedge_ranks = |r: &R3, piv: usize| -> (usize, usize, usize) {
            let kt = kt_from_abc(&r.abc);
            assert!(kt.t[piv].iter().all(|&x| x == 0), "folded slice must vanish");
            let (mut rows, words) = koszul_rows(&kt, 4);
            let e4 = rank_wide_legacy(&mut rows, words);
            let mut t8 = kt.t.clone();
            t8.remove(piv);
            let kt8 = KT { da: 8, db: 9, dc: 9, t: t8 };
            let (mut r3, w3) = koszul_rows(&kt8, 3);
            let h3 = rank_wide_legacy(&mut r3, w3);
            let (mut r4, w4) = koszul_rows(&kt8, 4);
            let h4 = rank_wide_legacy(&mut r4, w4);
            assert_eq!(e4, h3 + h4, "embedded p=4 == honest r3 + r4");
            (e4, h3, h4)
        };
        // gate 1: the action convention preserves T (27 terms).
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for _ in 0..20 {
            let e = mk(gl[(rnd() % 168) as usize], gl[(rnd() % 168) as usize], gl[(rnd() % 168) as usize]);
            let mut acc = [0u64; W];
            for i in 0..3 {
                for j in 0..3 {
                    for k in 0..3 {
                        let (a, b, c) = e.act(1 << (3 * i + j), 1 << (3 * j + k), 1 << (3 * k + i));
                        xor(&mut acc, &product_mask(a as u32, b as u32, c as u32));
                    }
                }
            }
            assert_eq!(acc, t3.abc, "sandwich action must fix T");
        }
        // gate 2: the fold data is a sandwich invariant of (m, v).
        for _ in 0..40 {
            let e = mk(gl[(rnd() % 168) as usize], gl[(rnd() % 168) as usize], gl[(rnd() % 168) as usize]);
            let (al, be, ga) = ((rnd() % 511 + 1) as u16, (rnd() % 511 + 1) as u16, (rnd() % 511 + 1) as u16);
            let v = (rnd() % 511 + 1) as u16;
            let (al2, be2, ga2) = e.act(al, be, ga);
            let v2 = act_v(&e, v);
            let mut r1 = t3;
            r1.xor_product(al as u32, be as u32, ga as u32);
            let mut r2 = t3;
            r2.xor_product(al2 as u32, be2 as u32, ga2 as u32);
            let f1 = fold_v(&r1, v as u32);
            let f2 = fold_v(&r2, v2 as u32);
            let w1 = wedge_ranks(&f1, (31 - (v as u32).leading_zeros()) as usize);
            let w2 = wedge_ranks(&f2, (31 - (v2 as u32).leading_zeros()) as usize);
            assert_eq!(w1, w2, "fold wedge data must be a sandwich invariant");
            assert_eq!(koszul_bound3(&f1, 4), koszul_bound3(&f2, 4), "koszul_bound3 invariant");
        }
        eprintln!("fold-lemma: gates passed (T fixed by 20 random sandwich elements; 40 random (m,v) transports agree)");
        let reps = first_product_reps();
        let v_rep: [u16; 4] = [0, 1 << 8, (1 << 4) | (1 << 8), 1 | (1 << 4) | (1 << 8)];
        for &rk in &ranks {
            let t0 = Instant::now();
            let v0 = v_rep[rk as usize];
            assert_eq!(rank3m(v0 as u32), rk);
            // Stab(v0) in (P,Q): P^T v0 Q^T == v0
            let mut stab: Vec<(u16, u16)> = Vec::new();
            for &p in &gl {
                let pt = m3_tr(p);
                for &q in &gl {
                    if m3_mul(m3_mul(pt, v0), m3_tr(q)) == v0 {
                        stab.push((p, q));
                    }
                }
            }
            let gsize = stab.len() * 168;
            // staged lex-min orbit reps of (al, be, ga) under Stab(v0) x GL3
            let mut alpha_min = [u16::MAX; 512];
            for &(p, q) in &stab {
                let (pt, qt) = (m3_tr(p), m3_tr(q));
                for al in 1u16..512 {
                    let im = m3_mul(m3_mul(pt, al), qt);
                    if im < alpha_min[al as usize] {
                        alpha_min[al as usize] = im;
                    }
                }
            }
            let mut orbit_reps: Vec<(u16, u16, u16, u64)> = Vec::new();
            for ar in 1u16..512 {
                if alpha_min[ar as usize] != ar {
                    continue;
                }
                let g1: Vec<(u16, u16)> = stab
                    .iter()
                    .copied()
                    .filter(|&(p, q)| m3_mul(m3_mul(m3_tr(p), ar), m3_tr(q)) == ar)
                    .collect();
                let mut beta_min = [u16::MAX; 512];
                for &(_, q) in &g1 {
                    let qit = m3_tr(inv[q as usize]);
                    for &r in &gl {
                        let rt = m3_tr(r);
                        for be in 1u16..512 {
                            let im = m3_mul(m3_mul(qit, be), rt);
                            if im < beta_min[be as usize] {
                                beta_min[be as usize] = im;
                            }
                        }
                    }
                }
                for br in 1u16..512 {
                    if beta_min[br as usize] != br {
                        continue;
                    }
                    let mut g2: Vec<(u16, u16, u16)> = Vec::new();
                    for &(p, q) in &g1 {
                        let qit = m3_tr(inv[q as usize]);
                        for &r in &gl {
                            if m3_mul(m3_mul(qit, br), m3_tr(r)) == br {
                                g2.push((p, q, r));
                            }
                        }
                    }
                    let mut gamma_min = [u16::MAX; 512];
                    for &(p, _, r) in &g2 {
                        let (pi, ri) = (inv[p as usize], inv[r as usize]);
                        for ga in 1u16..512 {
                            let im = act_gamma(pi, ri, ga);
                            if im < gamma_min[ga as usize] {
                                gamma_min[ga as usize] = im;
                            }
                        }
                    }
                    for ga in 1u16..512 {
                        if gamma_min[ga as usize] != ga {
                            continue;
                        }
                        let g3 = g2
                            .iter()
                            .filter(|&&(p, _, r)| act_gamma(inv[p as usize], inv[r as usize], ga) == ga)
                            .count();
                        assert_eq!(gsize % g3, 0);
                        orbit_reps.push((ar, br, ga, (gsize / g3) as u64));
                    }
                }
            }
            let total: u64 = orbit_reps.iter().map(|x| x.3).sum();
            assert_eq!(total, 511u64 * 511 * 511, "orbit sizes must partition the 511^3 products");
            eprintln!(
                "rank {rk}: v0 = {v0:#011b} |Stab(v0)| = {} |G| = {gsize} orbits = {} (sizes sum to 511^3) [{:.1}s]",
                stab.len(),
                orbit_reps.len(),
                t0.elapsed().as_secs_f64()
            );
            let piv = (31 - (v0 as u32).leading_zeros()) as usize;
            let base_f = fold_v(&t3, v0 as u32);
            let base = wedge_ranks(&base_f, piv);
            let base_k = koszul_bound3(&base_f, 4);
            println!("rank {rk}: base T|v: e4 {} h3 {} h4 {} koszul {base_k}", base.0, base.1, base.2);
            // evaluate every orbit
            let results: std::sync::Mutex<Vec<(usize, (usize, usize, usize), u32)>> =
                std::sync::Mutex::new(vec![(0, (0, 0, 0), 0); orbit_reps.len()]);
            let widx = AtomicUsize::new(0);
            std::thread::scope(|scope| {
                for _ in 0..threads {
                    scope.spawn(|| loop {
                        let i = widx.fetch_add(1, Ordering::Relaxed);
                        if i >= orbit_reps.len() {
                            break;
                        }
                        let (al, be, ga, _) = orbit_reps[i];
                        let mut r = t3;
                        r.xor_product(al as u32, be as u32, ga as u32);
                        let f = fold_v(&r, v0 as u32);
                        let w = wedge_ranks(&f, piv);
                        let k = koszul_bound3(&f, 4);
                        results.lock().unwrap()[i] = (i, w, k);
                    });
                }
            });
            let results = results.into_inner().unwrap();
            use std::collections::BTreeMap;
            let mut hist: BTreeMap<(i64, i64, i64, u32), (u64, u64)> = BTreeMap::new();
            let mut min_e4 = usize::MAX;
            let fname = format!("matmul/r22/fold_lemma_rank{rk}.txt");
            let mut out = String::new();
            out.push_str(&format!(
                "# v0 {v0} rank {rk} base e4 {} h3 {} h4 {} koszul {base_k}; columns: al be ga orbit e4 h3 h4 koszul rk(al) rk(be) rk(ga)\n",
                base.0, base.1, base.2
            ));
            for (i, w, k) in &results {
                let (al, be, ga, sz) = orbit_reps[*i];
                let key = (
                    base.0 as i64 - w.0 as i64,
                    base.1 as i64 - w.1 as i64,
                    base.2 as i64 - w.2 as i64,
                    *k,
                );
                let e = hist.entry(key).or_insert((0, 0));
                e.0 += 1;
                e.1 += sz;
                min_e4 = min_e4.min(w.0);
                out.push_str(&format!(
                    "{al} {be} {ga} {sz} {} {} {} {k} {} {} {}\n",
                    w.0,
                    w.1,
                    w.2,
                    rank3m(al as u32),
                    rank3m(be as u32),
                    rank3m(ga as u32)
                ));
            }
            std::fs::write(&fname, out).unwrap();
            println!("rank {rk}: (e4 drop, h3 drop, h4 drop, koszul) -> (orbits, products):");
            for (k, v) in &hist {
                println!("  {k:?}: {} orbits, {} products", v.0, v.1);
            }
            let killers: u64 = results
                .iter()
                .filter(|(_, _, k)| *k < 14)
                .map(|(i, _, _)| orbit_reps[*i].3)
                .sum();
            println!(
                "rank {rk}: min e4 {min_e4} (threshold 911); koszul<14 products: {killers} of {total}; table {fname} [{:.1}s]",
                t0.elapsed().as_secs_f64()
            );
            // transport check against the killer-dump convention: every
            // root x side x lambda (v = e8 + lambda) of matrix rank rk.
            let table: std::collections::HashMap<(u16, u16, u16), ((usize, usize, usize), u32)> = results
                .iter()
                .map(|(i, w, k)| {
                    let (al, be, ga, _) = orbit_reps[*i];
                    ((al, be, ga), (*w, *k))
                })
                .collect();
            let full: Vec<StabElem> = stab
                .iter()
                .flat_map(|&(p, q)| gl.iter().map(move |&r| (p, q, r)))
                .map(|(p, q, r)| mk(p, q, r))
                .collect();
            // one sandwich element carrying v -> v0, per v of rank rk
            let mut carry: Vec<Option<StabElem>> = vec![None; 512];
            for v in 1u16..512 {
                if rank3m(v as u32) != rk {
                    continue;
                }
                'outer: for &p in &gl {
                    for &q in &gl {
                        let e = mk(p, q, M3_ID);
                        if act_v(&e, v) == v0 {
                            carry[v as usize] = Some(e);
                            break 'outer;
                        }
                    }
                }
                assert!(carry[v as usize].is_some());
            }
            // --transport-roots FILE: use these "al,be,ga" triples (in
            // file order) instead of the orbit reps, e.g. the pre-fix 211
            // roots of the killer-dump; --transport-dump FILE: write the
            // predicted killers in the killer-dump line format.
            let roots: Vec<(u32, u32, u32)> = match get("--transport-roots") {
                Some(path) => std::fs::read_to_string(&path)
                    .unwrap()
                    .lines()
                    .filter(|l| !l.trim().is_empty())
                    .map(|l| {
                        let v: Vec<u32> = l.trim().split(',').map(|x| x.parse().unwrap()).collect();
                        (v[0], v[1], v[2])
                    })
                    .collect(),
                None => reps.iter().map(|r| (r.0, r.1, r.2)).collect(),
            };
            let dump = std::sync::Mutex::new(Vec::<String>::new());
            let t1 = Instant::now();
            let mism = AtomicUsize::new(0);
            let checked = AtomicUsize::new(0);
            let kill_ct = AtomicUsize::new(0);
            let widx = AtomicUsize::new(0);
            std::thread::scope(|scope| {
                for _ in 0..threads {
                    scope.spawn(|| loop {
                        let ri = widx.fetch_add(1, Ordering::Relaxed);
                        if ri >= roots.len() {
                            break;
                        }
                        let (al, be, ga) = roots[ri];
                        for side in 0..3usize {
                            let m = match side {
                                0 => (al as u16, be as u16, ga as u16),
                                1 => (be as u16, ga as u16, al as u16),
                                _ => (ga as u16, al as u16, be as u16),
                            };
                            let mut r = t3;
                            r.xor_product(m.0 as u32, m.1 as u32, m.2 as u32);
                            let own = koszul_bound3(&r, 4);
                            for lam in 0..256u32 {
                                let v = (1u32 << 8) | lam;
                                if rank3m(v) != rk {
                                    continue;
                                }
                                let f = fold_v(&r, v);
                                let w = wedge_ranks(&f, 8);
                                let k = koszul_bound3(&f, 4);
                                if k < 14 {
                                    kill_ct.fetch_add(1, Ordering::Relaxed);
                                }
                                if k < own {
                                    dump.lock().unwrap().push(format!(
                                        "root {ri} rep {al},{be},{ga} own {own} side {side} pivot 8 lam {lam} koszul {k}"
                                    ));
                                }
                                let e = carry[v as usize].unwrap();
                                let m2 = e.act(m.0, m.1, m.2);
                                let mut best = (u16::MAX, u16::MAX, u16::MAX);
                                for g in &full {
                                    let x = g.act(m2.0, m2.1, m2.2);
                                    if x < best {
                                        best = x;
                                    }
                                }
                                let tv = table.get(&best).copied();
                                checked.fetch_add(1, Ordering::Relaxed);
                                if tv != Some((w, k)) {
                                    mism.fetch_add(1, Ordering::Relaxed);
                                    eprintln!(
                                        "  MISMATCH root {ri} side {side} lam {lam}: direct {w:?}/{k} table {tv:?} canon {best:?}"
                                    );
                                }
                            }
                        }
                    });
                }
            });
            if let Some(path) = get("--transport-dump") {
                let mut lines = dump.into_inner().unwrap();
                lines.sort();
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&path).unwrap();
                use std::io::Write;
                for l in &lines {
                    writeln!(f, "{l}").unwrap();
                }
            }
            println!(
                "rank {rk}: transport check {} (root,side,lambda) triples, mismatches {}, direct koszul<14 count {} [{:.1}s]",
                checked.load(Ordering::Relaxed),
                mism.load(Ordering::Relaxed),
                kill_ct.load(Ordering::Relaxed),
                t1.elapsed().as_secs_f64()
            );
        }
        return;
    }
    if args.iter().any(|a| a == "--hyperplane-koszul") {
        // The three base values: koszul(T | ker phi) for every nonzero
        // covector phi on each side, grouped by matrix rank of phi (as a
        // 3x3 F2 matrix). The sandwich orbits on covectors are exactly the
        // rank classes, so each class should be constant — measured, not
        // assumed. Embedded convention (9-dim arrays, denominator C(8,p)),
        // matching the killer dump and the subadditivity argument.
        let masks = Masks::build();
        let t3 = R3::from_abc(&build_t3());
        fn rank3m(bits9: u32) -> u32 {
            let mut rows = [bits9 & 7, bits9 >> 3 & 7, bits9 >> 6 & 7];
            let mut rk = 0usize;
            for c in (0..3).rev() {
                if let Some(p) = (rk..3).find(|&i| rows[i] >> c & 1 == 1) {
                    rows.swap(rk, p);
                    for i in 0..3 {
                        if i != rk && rows[i] >> c & 1 == 1 {
                            rows[i] ^= rows[rk];
                        }
                    }
                    rk += 1;
                }
            }
            rk as u32
        }
        for side in 0..3usize {
            let sidx = STRIDE_IDX[side];
            let mut per_rank: std::collections::BTreeMap<u32, std::collections::BTreeMap<u32, u32>> =
                Default::default();
            for phi in 1u32..512 {
                let p = (31 - phi.leading_zeros()) as usize; // leading coordinate
                let rest = phi & !(1 << p);
                // lambda over others = coords != p in increasing order
                let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
                let mut lam = 0u32;
                for (bi, &c) in others.iter().enumerate() {
                    if rest >> c & 1 == 1 {
                        lam |= 1 << bi;
                    }
                }
                let lts = [t3.abc, t3.bca, t3.cab];
                let mut bases = lts;
                let mut slices = [[0u64; W]; 3];
                for l in 0..3 {
                    slices[l] = layout_slice(&lts[l], &masks, sidx[l], p);
                    for w in 0..W {
                        bases[l][w] ^= slices[l][w];
                    }
                }
                for (bi, &q) in others.iter().enumerate() {
                    if lam >> bi & 1 == 1 {
                        for l in 0..3 {
                            let sh = layout_shift(&slices[l], sidx[l], p, q);
                            for w in 0..W {
                                bases[l][w] ^= sh[w];
                            }
                        }
                    }
                }
                let folded = R3 { abc: bases[0], bca: bases[1], cab: bases[2] };
                let k = koszul_bound3(&folded, 4);
                *per_rank
                    .entry(rank3m(phi))
                    .or_default()
                    .entry(k)
                    .or_insert(0) += 1;
            }
            println!("side {side}: koszul(T|ker phi) by rank(phi): {:?}", per_rank);
        }
        return;
    }
    if args.iter().any(|a| a == "--killer-dump") {
        // For each root rep: enumerate the probe's folds (per side, LAST
        // ACTIVE pivot, all 2^8 lambdas — the probe's own convention) and
        // dump every KILLER: a fold whose koszul(p<=4) drops below the
        // node's own value (uniformly 14 at these roots). One line per
        // killer: root, rep, side, pivot, lambda, koszul(fold).
        let reps = first_product_reps();
        let masks = Masks::build();
        let t3 = build_t3();
        let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
        let out = std::sync::Mutex::new(Vec::<String>::new());
        let widx = AtomicUsize::new(0);
        let t0 = Instant::now();
        std::thread::scope(|scope| {
            for _ in 0..threads {
                scope.spawn(|| loop {
                    let i = widx.fetch_add(1, Ordering::Relaxed);
                    if i >= reps.len() {
                        break;
                    }
                    let (al, be, ga, _) = reps[i];
                    let mut r3 = R3::from_abc(&t3);
                    r3.xor_product(al, be, ga);
                    let own = koszul_bound3(&r3, 4);
                    let mut lines = Vec::new();
                    let layouts = [r3.abc, r3.bca, r3.cab];
                    for side in 0..3usize {
                        let sidx = STRIDE_IDX[side];
                        let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
                        let p = match (0..9).rev().find(|&p| {
                            !is_zero(&layout_slice(&layouts[major_layout], &masks, 0, p))
                        }) {
                            Some(p) => p,
                            None => continue,
                        };
                        let mut bases = layouts;
                        let mut slices = [[0u64; W]; 3];
                        for l in 0..3 {
                            slices[l] = layout_slice(&layouts[l], &masks, sidx[l], p);
                            for w in 0..W {
                                bases[l][w] ^= slices[l][w];
                            }
                        }
                        let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
                        let shifted: Vec<[T3; 3]> = others
                            .iter()
                            .map(|&q| {
                                let mut sh = [[0u64; W]; 3];
                                for l in 0..3 {
                                    sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                                }
                                sh
                            })
                            .collect();
                        for lam in 0..256u32 {
                            let mut m = bases;
                            for (bi, sh) in shifted.iter().enumerate() {
                                if lam >> bi & 1 == 1 {
                                    for l in 0..3 {
                                        for w in 0..W {
                                            m[l][w] ^= sh[l][w];
                                        }
                                    }
                                }
                            }
                            let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
                            let kf = koszul_bound3(&folded, 4);
                            if kf < own {
                                lines.push(format!(
                                    "root {i} rep {al},{be},{ga} own {own} side {side} pivot {p} lam {lam} koszul {kf}"
                                ));
                            }
                        }
                    }
                    out.lock().unwrap().extend(lines);
                });
            }
        });
        let mut lines = out.into_inner().unwrap();
        lines.sort();
        for l in &lines {
            println!("{l}");
        }
        eprintln!("killer-dump: {} killers across 211 roots ({:.0}s)", lines.len(), t0.elapsed().as_secs_f64());
        return;
    }
    if args.iter().any(|a| a == "--root-probe-deep") {
        let t: u32 = get("--target-bound").and_then(|v| v.parse().ok()).unwrap_or(15);
        let dmax: u32 = get("--depth").and_then(|v| v.parse().ok()).unwrap_or(6);
        let mut reps = first_product_reps();
        if let Some(path) = get("--root-filter") {
            // restrict to the rep triples "al,be,ga" listed one per line
            // (e.g. the 52 true orbits the pre-fix roots never covered)
            let keep: std::collections::HashSet<(u32, u32, u32)> = std::fs::read_to_string(&path)
                .unwrap()
                .lines()
                .filter(|l| !l.trim().is_empty())
                .map(|l| {
                    let v: Vec<u32> = l.trim().split(',').map(|x| x.parse().unwrap()).collect();
                    (v[0], v[1], v[2])
                })
                .collect();
            reps.retain(|r| keep.contains(&(r.0, r.1, r.2)));
            eprintln!("root filter {path}: {} of {} roots kept", reps.len(), keep.len());
            for (i, r) in reps.iter().enumerate() {
                eprintln!("  root {i} = {},{},{}", r.0, r.1, r.2);
            }
        }
        let masks = Masks::build();
        let t3 = build_t3();
        let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
        if args.iter().any(|a| a == "--probe-pool-test") {
            // gate: pooled == serial truth value on a few (root, t, depth)
            // default cases by rep index; --pool-test-cases "al,be,ga,t,d;..."
            // gives explicit products (e.g. the repaired roots).
            // case = al,be,ga,t,d[,expected]: without `expected` the serial
            // probe is run as the baseline (single-threaded — only for cheap
            // cases); with expected 0/1 the case runs POOLED ONLY and is
            // checked against that recorded verdict (e.g. a root already
            // proven by the fanned probe).
            let mut cases: Vec<(u32, u32, u32, u32, u32, Option<bool>)> = Vec::new();
            match get("--pool-test-cases") {
                Some(spec) => {
                    for c in spec.split(';') {
                        let v: Vec<u32> = c.split(',').map(|x| x.trim().parse().unwrap()).collect();
                        cases.push((v[0], v[1], v[2], v[3], v[4], v.get(5).map(|&x| x != 0)));
                    }
                }
                None => {
                    for &(ri, tt, dd) in &[(0usize, 14u32, 6u32), (0, 15, 1), (0, 16, 1), (0, 15, 2), (7, 15, 2), (0, 12, 6)] {
                        let (al, be, ga, _) = reps[ri];
                        cases.push((al, be, ga, tt, dd, None));
                    }
                }
            }
            for &(al, be, ga, tt, dd, expected) in &cases {
                let ri = format!("{al},{be},{ga}");
                let mut r3 = R3::from_abc(&t3);
                r3.xor_product(al, be, ga);
                let (baseline, ts, how) = match expected {
                    Some(e) => (e, 0.0, "recorded"),
                    None => {
                        let t0 = Instant::now();
                        let s = deep_probe(&r3, &masks, tt, dd);
                        (s, t0.elapsed().as_secs_f64(), "serial")
                    }
                };
                let t0 = Instant::now();
                let (pooled, run, skipped) = deep_probe_pool(&r3, &masks, tt, dd, threads);
                let tp = t0.elapsed().as_secs_f64();
                println!(
                    "root {ri} t={tt} depth={dd}: {how} {baseline} [{ts:.2}s] pooled {pooled} [{tp:.2}s; {run} tasks run, {skipped} skipped]"
                );
                assert_eq!(baseline, pooled, "pooled probe disagrees with {how}");
            }
            println!("probe-pool-test: all cases agree");
            return;
        }
        if args.iter().any(|a| a == "--probe-pool") {
            // sequential roots, each probe over the global work queue
            let max_roots: usize =
                get("--max-roots").and_then(|v| v.parse().ok()).unwrap_or(reps.len());
            let t0 = Instant::now();
            let (mut ok_c, mut fail_c) = (0u32, 0u32);
            for (i, &(al, be, ga, _)) in reps.iter().enumerate().take(max_roots) {
                let mut r3 = R3::from_abc(&t3);
                r3.xor_product(al, be, ga);
                let tr = Instant::now();
                let (ok, run, skipped) = deep_probe_pool(&r3, &masks, t, dmax, threads);
                if ok {
                    ok_c += 1;
                } else {
                    fail_c += 1;
                }
                eprintln!(
                    "  root {i} ({al},{be},{ga}) deep({t}) {} [{:.1}s; {run} tasks, {skipped} skipped] {}/{} ok={ok_c} fail={fail_c} ({:.0}s)",
                    if ok { "ok" } else { "FAILS" },
                    tr.elapsed().as_secs_f64(),
                    i + 1,
                    reps.len(),
                    t0.elapsed().as_secs_f64()
                );
            }
            eprintln!("deep-probe t={t} (pool): ok {ok_c} fail {fail_c} of {} ({:.0}s)", reps.len(), t0.elapsed().as_secs_f64());
            return;
        }
        if args.iter().any(|a| a == "--probe-par") {
            // sequential roots, each probe fanned across all threads —
            // no single-threaded tail. --max-roots N limits the sample.
            let max_roots: usize =
                get("--max-roots").and_then(|v| v.parse().ok()).unwrap_or(reps.len());
            let t0 = Instant::now();
            let mut ok_c = 0u32;
            let mut fail_c = 0u32;
            for (i, &(al, be, ga, _)) in reps.iter().enumerate().take(max_roots) {
                let mut r3 = R3::from_abc(&t3);
                r3.xor_product(al, be, ga);
                let tr = Instant::now();
                if deep_probe_par(&r3, &masks, t, dmax, threads) {
                    ok_c += 1;
                } else {
                    fail_c += 1;
                    eprintln!("  root {i} FAILS deep({t}) [{:.1}s]", tr.elapsed().as_secs_f64());
                }
                if (i + 1) % 16 == 0 {
                    eprintln!("  {}/211 ok={ok_c} fail={fail_c} ({:.0}s)", i + 1, t0.elapsed().as_secs_f64());
                }
            }
            eprintln!("deep-probe t={t}: ok {ok_c} fail {fail_c} of 211 ({:.0}s)", t0.elapsed().as_secs_f64());
            return;
        }
        let ok_n = AtomicU64::new(0);
        let fail_n = AtomicU64::new(0);
        let widx = AtomicUsize::new(0);
        let t0 = Instant::now();
        std::thread::scope(|scope| {
            for _ in 0..threads {
                scope.spawn(|| loop {
                    let i = widx.fetch_add(1, Ordering::Relaxed);
                    if i >= reps.len() {
                        break;
                    }
                    let (al, be, ga, _) = reps[i];
                    let mut r3 = R3::from_abc(&t3);
                    r3.xor_product(al, be, ga);
                    let tr = Instant::now();
                    let ok = deep_probe(&r3, &masks, t, dmax);
                    let d = if ok {
                        ok_n.fetch_add(1, Ordering::Relaxed) + fail_n.load(Ordering::Relaxed)
                    } else {
                        eprintln!("  root {i} FAILS deep({t}) [{:.1}s]", tr.elapsed().as_secs_f64());
                        fail_n.fetch_add(1, Ordering::Relaxed) + ok_n.load(Ordering::Relaxed)
                    } + 1;
                    if d % 16 == 0 {
                        eprintln!(
                            "  {d}/211 ok={} fail={} ({:.0}s)",
                            ok_n.load(Ordering::Relaxed),
                            fail_n.load(Ordering::Relaxed),
                            t0.elapsed().as_secs_f64()
                        );
                    }
                });
            }
        });
        eprintln!(
            "deep-probe t={t}: ok {} fail {} of 211 ({:.0}s)",
            ok_n.load(Ordering::Relaxed),
            fail_n.load(Ordering::Relaxed),
            t0.elapsed().as_secs_f64()
        );
        return;
    }
    if args.iter().any(|a| a == "--root-probe3") {
        let budget_s: f64 = get("--root-budget").and_then(|v| v.parse().ok()).unwrap_or(1200.0);
        let reps = first_product_reps();
        let masks = Masks::build();
        let t3 = build_t3();
        let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
        let hist_m = std::sync::Mutex::new(std::collections::BTreeMap::new());
        let widx = AtomicUsize::new(0);
        let done = AtomicU64::new(0);
        let t0 = Instant::now();
        std::thread::scope(|scope| {
            for _ in 0..threads {
                scope.spawn(|| loop {
                    let i = widx.fetch_add(1, Ordering::Relaxed);
                    if i >= reps.len() {
                        break;
                    }
                    let (al, be, ga, _) = reps[i];
                    let mut r3 = R3::from_abc(&t3);
                    r3.xor_product(al, be, ga);
                    let p2 = ply2_root_t(&r3, &masks, 15);
                    let key: String = if p2 >= 15 {
                        "15(ply2)".to_string()
                    } else {
                        let t_root = Instant::now();
                        match ply3_root_budget(&r3, &masks, 15, t_root, budget_s) {
                            Some(v) if v >= 15 => "15(ply3)".to_string(),
                            Some(v) => format!("{}(ply3-complete)", v.max(14)),
                            None => "unresolved".to_string(),
                        }
                    };
                    *hist_m.lock().unwrap().entry(key).or_insert(0u32) += 1;
                    let d = done.fetch_add(1, Ordering::Relaxed) + 1;
                    eprintln!("  {d}/211 root {i} -> {} ({:.0}s)", key_dbg(&hist_m), t0.elapsed().as_secs_f64());
                });
            }
        });
        eprintln!(
            "root ply-3 histogram: {:?} ({:.0}s)",
            hist_m.into_inner().unwrap(),
            t0.elapsed().as_secs_f64()
        );
        return;
    }
    if args.iter().any(|a| a == "--rank9-test") {
        let mut seed = 0x0badc0ffee123456u64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mask81 = (1u128 << 81) - 1;
        let mut cases: Vec<[u128; 9]> = Vec::new();
        for t in 0..200000 {
            let mut rows = [0u128; 9];
            let sparse = t % 3;
            for i in 0..9 {
                let mut v = ((rnd() as u128) << 64 | rnd() as u128) & mask81;
                if sparse == 1 {
                    v &= ((rnd() as u128) << 64 | rnd() as u128) & mask81;
                } else if sparse == 2 && i > 4 {
                    v = 0; // rank-deficient shapes
                }
                rows[i] = v;
            }
            cases.push(rows);
        }
        for (i, c) in cases.iter().enumerate() {
            let mut legacy_in = *c;
            let a = rank9_fast(c);
            let b = rank9_legacy(&mut legacy_in);
            assert_eq!(a, b, "rank9 mismatch at case {i}");
        }
        eprintln!("rank9-test: 200000 cases, ranks identical");
        let t0 = Instant::now();
        let mut acc = 0u64;
        for c in &cases {
            acc += rank9_fast(c) as u64;
        }
        let fast_ns = t0.elapsed().as_secs_f64() / cases.len() as f64 * 1e9;
        let t1 = Instant::now();
        let mut acc2 = 0u64;
        for c in &cases {
            let mut m = *c;
            acc2 += rank9_legacy(&mut m) as u64;
        }
        let slow_ns = t1.elapsed().as_secs_f64() / cases.len() as f64 * 1e9;
        eprintln!(
            "  fast {fast_ns:.1} ns/call | legacy {slow_ns:.1} ns/call | speedup {:.2}x (checksums {acc}/{acc2})",
            slow_ns / fast_ns
        );
        return;
    }
    if args.iter().any(|a| a == "--m4r-test") {
        // gate: M4R rank must equal the legacy elimination on random matrices
        let mut seed = 0xfeedfacecafebeefu64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let t0 = Instant::now();
        for trial in 0..300 {
            let n = (rnd() % 200 + 1) as usize;
            let words = (rnd() % 20 + 1) as usize;
            let density = rnd() % 100;
            let mut m: Vec<Vec<u64>> = (0..n)
                .map(|_| {
                    (0..words)
                        .map(|_| if rnd() % 100 < density { rnd() } else { 0 })
                        .collect()
                })
                .collect();
            let mut m2 = m.clone();
            let r_new = rank_wide(&mut m, words);
            let r_old = rank_wide_legacy(&mut m2, words);
            assert_eq!(r_new, r_old, "M4R rank mismatch on trial {trial}");
        }
        eprintln!("m4r-test: 300 random matrices, ranks identical ({:.1}s)", t0.elapsed().as_secs_f64());
        // timing on koszul-shaped matrices (1134 x 18 words)
        for name in ["m4r", "legacy"] {
            let mut seed2 = 7u64;
            let mut rnd2 = move || {
                seed2 ^= seed2 << 13;
                seed2 ^= seed2 >> 7;
                seed2 ^= seed2 << 17;
                seed2
            };
            let t1 = Instant::now();
            for _ in 0..20 {
                let mut m: Vec<Vec<u64>> =
                    (0..1134).map(|_| (0..18).map(|_| rnd2()).collect()).collect();
                if name == "m4r" {
                    rank_wide(&mut m, 18);
                } else {
                    rank_wide_legacy(&mut m, 18);
                }
            }
            eprintln!("  {name}: {:.2} ms/elimination (1134x1152)", t1.elapsed().as_secs_f64() / 20.0 * 1000.0);
        }
        return;
    }
    if args.iter().any(|a| a == "--root-probe2") {
        // ply-2: per root, 1 + min over folds of koszul_probe3(fold, 14);
        // >= 15 everywhere <=> r=15 falls at the 211 roots.
        let reps = first_product_reps();
        let masks = Masks::build();
        let t3 = build_t3();
        let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
        let hist_m = std::sync::Mutex::new(std::collections::BTreeMap::new());
        let widx = AtomicUsize::new(0);
        let done = AtomicU64::new(0);
        let t0 = Instant::now();
        std::thread::scope(|scope| {
            for _ in 0..threads {
                scope.spawn(|| loop {
                    let i = widx.fetch_add(1, Ordering::Relaxed);
                    if i >= reps.len() {
                        break;
                    }
                    let (al, be, ga, _) = reps[i];
                    let mut r3 = R3::from_abc(&t3);
                    r3.xor_product(al, be, ga);
                    let best = ply2_root(&r3, &masks);
                    *hist_m.lock().unwrap().entry(best).or_insert(0u32) += 1;
                    let d = done.fetch_add(1, Ordering::Relaxed) + 1;
                    if d % 16 == 0 {
                        eprintln!("  {d}/211 done ({:.0}s)", t0.elapsed().as_secs_f64());
                    }
                });
            }
        });
        let hist = hist_m.into_inner().unwrap();
        eprintln!("root ply-2 histogram: {:?} ({:.0}s)", hist, t0.elapsed().as_secs_f64());
        return;
    }
    if false {
        // (retired serial ply-2 body below, kept for reference)
        let reps = first_product_reps();
        let masks = Masks::build();
        let t3 = build_t3();
        let mut hist = std::collections::BTreeMap::new();
        let t0 = Instant::now();
        for (i, &(al, be, ga, _)) in reps.iter().enumerate() {
            let mut r3 = R3::from_abc(&t3);
            r3.xor_product(al, be, ga);
            // inline the fold loop of koszul_probe3 but with probe leaves
            let mut best = 0u32;
            let layouts = |r: &R3| [r.abc, r.bca, r.cab];
            for side in 0..3usize {
                let sidx = STRIDE_IDX[side];
                let major_layout = sidx.iter().position(|&x| x == 0).unwrap();
                let lts = layouts(&r3);
                let p = match (0..9)
                    .rev()
                    .find(|&p| !is_zero(&layout_slice(&lts[major_layout], masks_ref(&masks), 0, p)))
                {
                    Some(p) => p,
                    None => continue,
                };
                let mut bases = lts;
                let mut slices = [[0u64; W]; 3];
                for l in 0..3 {
                    slices[l] = layout_slice(&lts[l], &masks, sidx[l], p);
                    for w in 0..W {
                        bases[l][w] ^= slices[l][w];
                    }
                }
                let others: Vec<usize> = (0..9).filter(|&x| x != p).collect();
                let shifted: Vec<[T3; 3]> = others
                    .iter()
                    .map(|&q| {
                        let mut sh = [[0u64; W]; 3];
                        for l in 0..3 {
                            sh[l] = layout_shift(&slices[l], sidx[l], p, q);
                        }
                        sh
                    })
                    .collect();
                let mut worst = u32::MAX;
                for lam in 0..256u32 {
                    let mut m = bases;
                    for (bi, sh) in shifted.iter().enumerate() {
                        if lam >> bi & 1 == 1 {
                            for l in 0..3 {
                                for w in 0..W {
                                    m[l][w] ^= sh[l][w];
                                }
                            }
                        }
                    }
                    let folded = R3 { abc: m[0], bca: m[1], cab: m[2] };
                    let pv = koszul_probe3(&folded, &masks, 4, 14);
                    worst = worst.min(pv);
                    if 1 + worst < 15 {
                        break;
                    }
                }
                if worst != u32::MAX {
                    best = best.max(1 + worst);
                }
                if best >= 15 {
                    break;
                }
            }
            *hist.entry(best).or_insert(0u32) += 1;
            if i % 16 == 0 {
                eprintln!("  root {i}: ply2 {best} ({:.0}s)", t0.elapsed().as_secs_f64());
            }
        }
        eprintln!("root ply-2 histogram: {:?} ({:.0}s)", hist, t0.elapsed().as_secs_f64());
        return;
    }
    if args.iter().any(|a| a == "--root-probe") {
        // tier-2 measurement: koszul-leaf 1-ply probe on all 211 roots;
        // >= 15 everywhere means r=15 falls at 211 nodes.
        let reps = first_product_reps();
        let masks = Masks::build();
        let t3 = build_t3();
        let mut hist = std::collections::BTreeMap::new();
        let t0 = Instant::now();
        for (i, &(al, be, ga, _)) in reps.iter().enumerate() {
            let mut r3 = R3::from_abc(&t3);
            r3.xor_product(al, be, ga);
            let b = koszul_probe3(&r3, &masks, 4, 15);
            *hist.entry(b).or_insert(0u32) += 1;
            if i % 32 == 0 {
                eprintln!("  root {i}: probe {b} ({:.0}s elapsed)", t0.elapsed().as_secs_f64());
            }
        }
        eprintln!("root koszul-probe histogram: {:?} ({:.0}s)", hist, t0.elapsed().as_secs_f64());
        return;
    }
    if args.iter().any(|a| a == "--koszul-p-profile") {
        // per-p koszul strength and cost on level-2 residuals
        let mut seed = 0x123456789abcdefu64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for p in 1..=4usize {
            let mut min_k = usize::MAX;
            let mut sum = 0usize;
            let n = 24;
            let t0 = Instant::now();
            for _ in 0..n {
                let mut r3 = R3::from_abc(&build_t3());
                for _ in 0..2 {
                    r3.xor_product(
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                        (rnd() % 511 + 1) as u32,
                    );
                }
                let kt = kt_from_abc(&r3.abc);
                let mut best = 0usize;
                for side in 1..=3u8 {
                    let ts = with_side_first(&kt, side);
                    best = best.max(koszul_side(&ts, p));
                }
                min_k = min_k.min(best);
                sum += best;
            }
            let per = t0.elapsed().as_secs_f64() / n as f64 * 1000.0;
            eprintln!(
                "p={p}: koszul mean {:.2} min {min_k} cost {per:.2} ms/eval (3 sides)",
                sum as f64 / n as f64
            );
        }
        return;
    }
    if args.iter().any(|a| a == "--lemma-decay") {
        let reps = first_product_reps();
        let (masks_p, pos_p, _mq, _pq) = wedge_indices(9, 4);
        let mut seed = 0x9e3779b97f4a7c15u64;
        let mut rnd = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for ri in [0usize, 40, 90, 140, 200] {
            let (al, be, ga, ref stab) = reps[ri.min(reps.len() - 1)];
            let mut r1 = R3::from_abc(&build_t3());
            r1.xor_product(al, be, ga);
            let kt1 = kt_from_abc(&r1.abc);
            // learn on the strongest side at p=4
            let mut best_side = 1u8;
            let mut best_v = 0usize;
            for side in 1..=3u8 {
                let ts = with_side_first(&kt1, side);
                let (mut rows, words) = koszul_rows(&ts, 4);
                let v = rank_wide(&mut rows, words);
                if v > best_v {
                    best_v = v;
                    best_side = side;
                }
            }
            let lem = learn_lemma(&kt1, best_side, 4).unwrap();
            let fresh1 = (lem.v + 69) / 70;
            eprintln!(
                "root {ri}: rep=({al},{be},{ga}) |stab|={} lemma side {} v={} (koszul1={})",
                stab.len(),
                best_side,
                lem.v,
                fresh1
            );
            let mut n = 0;
            let mut sum_fresh = 0u32;
            let mut sum_trans = 0u32;
            let mut hist = [0u32; 8]; // decay 0..7+
            while n < 60 {
                let m2a = (rnd() % 511 + 1) as u16;
                let m2b = (rnd() % 511 + 1) as u16;
                let m2g = (rnd() % 511 + 1) as u16;
                let mut r2 = r1;
                r2.xor_product(m2a as u32, m2b as u32, m2g as u32);
                let fresh = koszul_bound3(&r2, 4);
                let trans = lem.bound(&[(m2a, m2b, m2g)], &masks_p, &pos_p);
                let decay = fresh.saturating_sub(trans) as usize;
                hist[decay.min(7)] += 1;
                sum_fresh += fresh;
                sum_trans += trans;
                n += 1;
            }
            eprintln!(
                "  60 samples: mean fresh {:.2} mean transferred {:.2} decay hist {:?}",
                sum_fresh as f64 / 60.0,
                sum_trans as f64 / 60.0,
                hist
            );
        }
        return;
    }
    let t_reps = Instant::now();
    let reps = first_product_reps();
    let stab_sizes: Vec<usize> = reps.iter().map(|r| r.3.len()).collect();
    eprintln!(
        "first-product orbit reps: {} (of 133432831 products; {:.1}s); stab sizes min {} med {} max {}",
        reps.len(),
        t_reps.elapsed().as_secs_f64(),
        stab_sizes.iter().min().unwrap(),
        { let mut v = stab_sizes.clone(); v.sort(); v[v.len() / 2] },
        stab_sizes.iter().max().unwrap()
    );

    struct Tally { nodes: u64, prune_flat: u64, prune_sub: u64, prune_koszul: u64, prune_strassen: u64, capped: bool }
    let mut s = Tally { nodes: 0, prune_flat: 0, prune_sub: 0, prune_koszul: 0, prune_strassen: 0, capped: false };

    let full: u32 = (511 << 18) | (511 << 9) | 511;
    let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
    // work units: one per first-product orbit representative (with stab)
    let units: Vec<(u32, u32, u32, Vec<StabElem>)> = reps;
    let shared = Shared {
        capped: AtomicBool::new(false),
        found: AtomicBool::new(false),
        nodes: AtomicU64::new(0),
        prune_flat: AtomicU64::new(0),
        prune_sub: AtomicU64::new(0),
        prune_koszul: AtomicU64::new(0),
        prune_strassen: AtomicU64::new(0),
        work: AtomicUsize::new(0),
    };
    let masks = Masks::build();
    let r3_root = R3::from_abc(&t);
    let start = Instant::now();
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let mut w = Search {
                    masks: &masks,
                    koszul,
                    koszul_min_remaining,
                    stab: &[],
                    strassen: use_strassen,
                    deep_probe: deep_probe_d,
                    chosen: Vec::new(),
                    level2_remaining: r - 1,
                    nodes: 0,
                    prune_flat: 0,
                    prune_sub: 0,
                    prune_koszul: 0,
                    prune_strassen: 0,
                    sub_probe,
                    probe_min_remaining,
                    cap,
                    start,
                    capped: false,
                    shared: &shared,
                };
                loop {
                    let u = shared.work.fetch_add(1, Ordering::Relaxed);
                    if u >= units.len()
                        || shared.capped.load(Ordering::Relaxed)
                        || shared.found.load(Ordering::Relaxed)
                    {
                        break;
                    }
                    let (al, be, ga, ref stab_elems) = units[u];
                    let first_id = (al << 18) | (be << 9) | ga;
                    let mut nr = r3_root;
                    nr.xor_product(al, be, ga);
                    w.stab = stab_elems;
                    if w.dfs(&nr, r - 1, full + 1, first_id) {
                        shared.found.store(true, Ordering::Relaxed);
                    }
                    w.stab = &[];
                }
                shared.nodes.fetch_add(w.nodes, Ordering::Relaxed);
                shared.prune_flat.fetch_add(w.prune_flat, Ordering::Relaxed);
                shared.prune_sub.fetch_add(w.prune_sub, Ordering::Relaxed);
            });
        }
    });
    let found = shared.found.load(Ordering::Relaxed);
    s.nodes = shared.nodes.load(Ordering::Relaxed);
    s.prune_flat = shared.prune_flat.load(Ordering::Relaxed);
    s.prune_sub = shared.prune_sub.load(Ordering::Relaxed);
    s.prune_koszul = shared.prune_koszul.load(Ordering::Relaxed);
    s.prune_strassen = shared.prune_strassen.load(Ordering::Relaxed);
    s.capped = shared.capped.load(Ordering::Relaxed);

    let el = start.elapsed().as_secs_f64();
    if found {
        println!("r={r}: SAT?! — a scheme surfaced; INVESTIGATE (should be impossible for r<20)");
    } else if s.capped {
        println!(
            "r={r}: CAP ({} nodes, {:.1}s, prunes flat {} sub {} koszul {} strassen {})",
            s.nodes, el, s.prune_flat, s.prune_sub, s.prune_koszul, s.prune_strassen
        );
    } else {
        println!(
            "r={r}: UNSAT — exhausted ({} nodes, {:.1}s, prunes flat {} sub {} koszul {} strassen {}) => rank_F2(<3,3,3>) > {}",
            s.nodes,
            el,
            s.prune_flat,
            s.prune_sub,
            s.prune_koszul,
            s.prune_strassen,
            r
        );
    }
}
