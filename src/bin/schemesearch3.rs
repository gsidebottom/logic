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

fn rank_wide(rows: &mut Vec<Vec<u64>>, words: usize) -> usize {
    let n = rows.len();
    let mut rk = 0usize;
    for c in 0..words * 64 {
        let (w, b) = (c / 64, c % 64);
        if let Some(p) = (rk..n).find(|&i| rows[i][w] >> b & 1 == 1) {
            rows.swap(rk, p);
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
            rk += 1;
            if rk == n {
                break;
            }
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

/// Koszul flattening bound on side A with parameter p (verbatim port of
/// subgame.rs koszul_side; valid over any field, signs vanish over F2).
fn koszul_side(t: &KT, p: usize) -> usize {
    let (da, db, dc) = (t.da, t.db, t.dc);
    if da < 3 || p == 0 || p + 2 > da {
        return 0;
    }
    use std::collections::HashMap;
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
fn first_product_reps() -> Vec<(u32, u32, u32)> {
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
            // stabilizer triples fixing (ar, br)
            let mut stab2: Vec<(u16, u16)> = Vec::new(); // (P, R)
            for &(p, q) in &stab {
                let qit = m3_tr(m3_inv(&gl, q));
                for &r in &gl {
                    if m3_mul(m3_mul(qit, br), m3_tr(r)) == br {
                        stab2.push((p, r));
                    }
                }
            }
            // gamma reps: min over stab2: gamma -> P^-1 gamma R^-1
            let mut gamma_min = [u16::MAX; 512];
            for &(p, r) in &stab2 {
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
                if gamma_min[ga as usize] == ga {
                    reps.push((ar as u32, br as u32, ga as u32));
                }
            }
        }
    }
    reps
}

struct Shared {
    capped: AtomicBool,
    found: AtomicBool,
    nodes: AtomicU64,
    prune_flat: AtomicU64,
    prune_sub: AtomicU64,
    prune_koszul: AtomicU64,
    work: AtomicUsize,
}

struct Search<'a> {
    masks: &'a Masks,
    koszul: usize,             // 0 = off; else max p
    koszul_min_remaining: u32, // apply only at shallow nodes
    nodes: u64,
    prune_flat: u64,
    prune_sub: u64,
    prune_koszul: u64,
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
    let koszul_min_remaining: u32 =
        get("--koszul-min-remaining").and_then(|v| v.parse().ok()).unwrap_or(r.saturating_sub(1));

    let t = build_t3();
    assert_eq!(max_flatten(&t), 9, "matmul flattening sanity");

    let t_reps = Instant::now();
    let reps = first_product_reps();
    eprintln!(
        "first-product orbit reps: {} (of 133432831 products; {:.1}s)",
        reps.len(),
        t_reps.elapsed().as_secs_f64()
    );

    struct Tally { nodes: u64, prune_flat: u64, prune_sub: u64, prune_koszul: u64, capped: bool }
    let mut s = Tally { nodes: 0, prune_flat: 0, prune_sub: 0, prune_koszul: 0, capped: false };

    let full: u32 = (511 << 18) | (511 << 9) | 511;
    let threads: usize = get("--threads").and_then(|v| v.parse().ok()).unwrap_or(12);
    // work units: one per first-product orbit representative
    let units: Vec<(u32, u32, u32)> = reps;
    let shared = Shared {
        capped: AtomicBool::new(false),
        found: AtomicBool::new(false),
        nodes: AtomicU64::new(0),
        prune_flat: AtomicU64::new(0),
        prune_sub: AtomicU64::new(0),
        prune_koszul: AtomicU64::new(0),
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
                    nodes: 0,
                    prune_flat: 0,
                    prune_sub: 0,
                    prune_koszul: 0,
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
                    let (al, be, ga) = units[u];
                    let first_id = (al << 18) | (be << 9) | ga;
                    let mut nr = r3_root;
                    nr.xor_product(al, be, ga);
                    if w.dfs(&nr, r - 1, full + 1, first_id) {
                        shared.found.store(true, Ordering::Relaxed);
                    }
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
    s.capped = shared.capped.load(Ordering::Relaxed);

    let el = start.elapsed().as_secs_f64();
    if found {
        println!("r={r}: SAT?! — a scheme surfaced; INVESTIGATE (should be impossible for r<20)");
    } else if s.capped {
        println!(
            "r={r}: CAP ({} nodes, {:.1}s, prunes flat {} sub {} koszul {})",
            s.nodes, el, s.prune_flat, s.prune_sub, s.prune_koszul
        );
    } else {
        println!(
            "r={r}: UNSAT — exhausted ({} nodes, {:.1}s, prunes flat {} sub {} koszul {}) => rank_F2(<3,3,3>) > {}",
            s.nodes,
            el,
            s.prune_flat,
            s.prune_sub,
            s.prune_koszul,
            r
        );
    }
}
