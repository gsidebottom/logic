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

fn rank9(rows: &mut [u128; 9]) -> u32 {
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
    rank9(&mut rows)
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

fn rank_wide(rows: &mut Vec<Vec<u64>>, words: usize) -> usize {
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

/// Koszul wedge matrix rows for tensor t (side already rotated to A-first).
fn koszul_rows(t: &KT, p: usize) -> (Vec<Vec<u64>>, usize) {
    let (da, db, dc) = (t.da, t.db, t.dc);
    let (masks_p, pos_p, _masks_q, pos_q) = wedge_indices(da, p);
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
    let rk = rank_wide(&mut rows, words);
    let denom = binom(da - 1, p);
    (rk + denom - 1) / denom
}

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
/// gamma -> P^-1 gamma R^-1 (subgame.rs convention, tensor-verified there).
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
            m3_mul(m3_mul(self.pi, ga), self.ri),
        )
    }
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
                    let im = m3_mul(m3_mul(pi, ga), ri);
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
                        if m3_mul(m3_mul(pi, ga), ri) == ga {
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
    rank9(&mut fa).max(rank9(&mut fb)).max(rank9(&mut fc))
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
            if self.dfs(&nr, remaining - 1, id, skip) {
                return true;
            }
            if self.capped {
                return false;
            }
        }
        false
    }
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
