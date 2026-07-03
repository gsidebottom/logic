//! ANF (XOR-of-cubic-AND) constraint systems + stochastic local search.
//!
//! Built for the Brent equations of fast matrix multiplication (mod 2):
//! finding an `<n1,n2,n3>` scheme with `r` products means solving
//!
//! ```text
//!   XOR_m  alpha[m][a,b] & beta[m][c,d] & gamma[m][p,q]
//!        = [b==c][a==p][d==q]        for all (a,b,c,d,p,q)
//! ```
//!
//! i.e. `(n1*n2*n3)^2` cubic XOR equations over `r*(n1*n2+n2*n3+n1*n3)`
//! variables (3x3, r=23: 729 equations / 621 vars).  The search runs on this
//! native representation — the CNF encoding (Heule–Kauers–Seidl SAT'19) pays
//! a 43x variable blowup (26,541 vars) that local search then wanders
//! through; here a flip touches exactly the equations containing the
//! variable, and the monomial toggles iff its two partner bits are 1.
//!
//! Soundness: any claimed solution is re-checked by [`verify`], a from-
//! scratch recomputation independent of the incremental search state.

use rayon::prelude::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Instant;

// ---------------------------------------------------------------- rng

/// splitmix64-seeded xorshift* — fast, adequate for SLS move sampling.
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        // splitmix64 scramble so nearby seeds give unrelated streams
        let mut z = seed.wrapping_add(0x9e3779b97f4a7c15);
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        Rng((z ^ (z >> 31)) | 1)
    }
    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545f4914f6cdd1d)
    }
    /// uniform in `0..n` (Lemire multiply-shift)
    #[inline]
    pub fn below(&mut self, n: usize) -> usize {
        ((self.next_u64() as u128 * n as u128) >> 64) as usize
    }
    #[inline]
    pub fn f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / (1u64 << 53) as f64
    }
}

// ---------------------------------------------------------------- system

#[derive(Clone, Copy)]
pub struct Adj {
    pub eq: u32,
    pub p1: u32,
    pub p2: u32,
}

/// A cubic-monomial parity system in CSR form.
pub struct Anf {
    pub nvars: usize,
    pub eq_off: Vec<u32>,
    pub mons: Vec<[u32; 3]>,
    pub rhs: Vec<u8>,
    /// per-equation deduped variable lists (noise moves)
    pub eqv_off: Vec<u32>,
    pub eqv: Vec<u32>,
    /// var -> (eq, partner, partner)
    pub adj_off: Vec<u32>,
    pub adj: Vec<Adj>,
}

impl Anf {
    pub fn new(nvars: usize, eqs: Vec<(Vec<[u32; 3]>, u8)>) -> Anf {
        let ne = eqs.len();
        let mut eq_off = Vec::with_capacity(ne + 1);
        let mut mons = Vec::new();
        let mut rhs = Vec::with_capacity(ne);
        let mut eqv_off = Vec::with_capacity(ne + 1);
        let mut eqv = Vec::new();
        let mut deg = vec![0u32; nvars];
        eq_off.push(0);
        eqv_off.push(0);
        for (ms, rh) in &eqs {
            let mut vs: Vec<u32> = Vec::with_capacity(ms.len() * 3);
            for m in ms {
                mons.push(*m);
                for &v in m {
                    deg[v as usize] += 3; // upper bound; adj entry per position
                    vs.push(v);
                }
            }
            vs.sort_unstable();
            vs.dedup();
            eqv.extend_from_slice(&vs);
            eq_off.push(mons.len() as u32);
            eqv_off.push(eqv.len() as u32);
            rhs.push(*rh);
        }
        // adjacency: one entry per (monomial, position)
        let mut adj_off = vec![0u32; nvars + 1];
        let mut cnt = vec![0u32; nvars];
        for e in 0..ne {
            for i in eq_off[e]..eq_off[e + 1] {
                for &v in &mons[i as usize] {
                    cnt[v as usize] += 1;
                }
            }
        }
        for v in 0..nvars {
            adj_off[v + 1] = adj_off[v] + cnt[v];
        }
        let mut adj = vec![
            Adj { eq: 0, p1: 0, p2: 0 };
            adj_off[nvars] as usize
        ];
        let mut fill = adj_off.clone();
        for e in 0..ne {
            for i in eq_off[e]..eq_off[e + 1] {
                let [x, y, z] = mons[i as usize];
                for (v, p1, p2) in [(x, y, z), (y, x, z), (z, x, y)] {
                    let f = &mut fill[v as usize];
                    adj[*f as usize] = Adj { eq: e as u32, p1, p2 };
                    *f += 1;
                }
            }
        }
        Anf { nvars, eq_off, mons, rhs, eqv_off, eqv, adj_off, adj }
    }

    pub fn neqs(&self) -> usize {
        self.rhs.len()
    }
}

/// From-scratch check: number of violated equations (independent of any
/// incremental search state — the soundness gate for claimed schemes).
pub fn verify(anf: &Anf, bits: &[u8]) -> usize {
    let mut bad = 0;
    for e in 0..anf.neqs() {
        let mut acc = 0u8;
        for i in anf.eq_off[e]..anf.eq_off[e + 1] {
            let [x, y, z] = anf.mons[i as usize];
            acc ^= bits[x as usize] & bits[y as usize] & bits[z as usize];
        }
        bad += (acc != anf.rhs[e]) as usize;
    }
    bad
}

// ---------------------------------------------------------------- brent

#[derive(Clone, Copy)]
pub struct Dims {
    pub n1: usize,
    pub n2: usize,
    pub n3: usize,
    pub r: usize,
}

impl Dims {
    pub fn nvars(&self) -> usize {
        self.r * (self.n1 * self.n2 + self.n2 * self.n3 + self.n1 * self.n3)
    }
    pub fn a_idx(&self, m: usize, a: usize, b: usize) -> u32 {
        (m * self.n1 * self.n2 + a * self.n2 + b) as u32
    }
    pub fn b_idx(&self, m: usize, c: usize, d: usize) -> u32 {
        (self.r * self.n1 * self.n2 + m * self.n2 * self.n3 + c * self.n3 + d)
            as u32
    }
    pub fn g_idx(&self, m: usize, p: usize, q: usize) -> u32 {
        (self.r * (self.n1 * self.n2 + self.n2 * self.n3)
            + m * self.n1 * self.n3
            + p * self.n3
            + q) as u32
    }
}

/// The Brent-equation ANF system for an `<n1,n2,n3>` scheme with `r`
/// products (mod 2).
pub fn brent(d: Dims) -> Anf {
    let mut eqs = Vec::with_capacity((d.n1 * d.n2 * d.n3).pow(2));
    for a in 0..d.n1 {
        for b in 0..d.n2 {
            for c in 0..d.n2 {
                for dd in 0..d.n3 {
                    for p in 0..d.n1 {
                        for q in 0..d.n3 {
                            let rh = (b == c && a == p && dd == q) as u8;
                            let ms = (0..d.r)
                                .map(|m| {
                                    [
                                        d.a_idx(m, a, b),
                                        d.b_idx(m, c, dd),
                                        d.g_idx(m, p, q),
                                    ]
                                })
                                .collect();
                            eqs.push((ms, rh));
                        }
                    }
                }
            }
        }
    }
    Anf::new(d.nvars(), eqs)
}

/// Laderman 1976 (3x3x3, r=23) mod 2, in this module's variable order.
/// Bit string generated by matmul/brent.py from the symbolically-verified
/// transcription of Bull. AMS 82(1):126-128; re-verified by the `schemes`
/// test against [`brent`].
pub const LADERMAN_BITS: &str = "111110011100100000000010000100110000000110000100000000100000110100000100000000110111011110000000010001000011001000001001000000000000011001011000001001000000011000010000000000001000000100000000000100000000001000010000010010000110111101110010000110000000100000000101001000001001000101000000000001000101111110000010110000010010000000100000000110000001101000001001000000101000100000000000010001000000010000000000000001010000000000110000000100000010110000010010000111110101001000101000000101001000001001000000000000100010000110000000110111101110010000010001101000000101000001001000100000000000010000000001000000000010000000001";

/// Strassen (2x2x2, r=7) mod 2.
pub const STRASSEN_BITS: &str =
    "100100111000000111001010010110011000010110100001110000111001001101011010110000011000";

pub fn bits_of(s: &str) -> Vec<u8> {
    s.bytes().map(|b| (b - b'0') as u8).collect()
}

// ---------------------------------------------------------------- pairing

/// Heule et al. "method 1": assign the n^3 type-3 terms `(a,b,d)` (the
/// RHS-1 equations) to products so `n^3 - r` products hold 2 terms
/// (pairwise different in ALL coordinates) and the rest hold 1.  Returns
/// frozen `(var, 1)` units, or None if the shuffle fails (retry).
pub fn random_pairing(d: Dims, rng: &mut Rng) -> Option<Vec<(u32, u8)>> {
    assert!(d.n1 == d.n2 && d.n2 == d.n3, "pairing assumes square");
    let n = d.n1;
    let nterms = n * n * n;
    assert!(nterms >= d.r, "r too large for pairing");
    let npairs = nterms - d.r;
    let mut terms: Vec<(usize, usize, usize)> = Vec::with_capacity(nterms);
    for a in 0..n {
        for b in 0..n {
            for dd in 0..n {
                terms.push((a, b, dd));
            }
        }
    }
    // Fisher-Yates
    for i in (1..terms.len()).rev() {
        terms.swap(i, rng.below(i + 1));
    }
    let mut used = vec![false; nterms];
    let mut groups: Vec<Vec<(usize, usize, usize)>> = Vec::with_capacity(d.r);
    for i in 0..nterms {
        if groups.len() == npairs {
            break;
        }
        if used[i] {
            continue;
        }
        for j in i + 1..nterms {
            if used[j] {
                continue;
            }
            let (t, u) = (terms[i], terms[j]);
            if t.0 != u.0 && t.1 != u.1 && t.2 != u.2 {
                groups.push(vec![t, u]);
                used[i] = true;
                used[j] = true;
                break;
            }
        }
    }
    if groups.len() != npairs {
        return None;
    }
    for i in 0..nterms {
        if !used[i] {
            groups.push(vec![terms[i]]);
        }
    }
    debug_assert_eq!(groups.len(), d.r);
    let mut frozen = Vec::new();
    for (m, g) in groups.iter().enumerate() {
        for &(a, b, dd) in g {
            frozen.push((d.a_idx(m, a, b), 1));
            frozen.push((d.b_idx(m, b, dd), 1));
            frozen.push((d.g_idx(m, a, dd), 1));
        }
    }
    Some(frozen)
}

// ---------------------------------------------------------------- closure

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Block {
    Alpha,
    Beta,
    Gamma,
}

const RHS_BIT: u32 = 63;

/// RREF over GF(2); rows pack coefficient bits 0..ncols and rhs at bit 63.
/// Returns (pivot rows as (col, row), #contradiction rows). After full
/// reduction each pivot row's remaining coefficient bits are free columns.
fn gauss_rref(rows: &mut Vec<u64>, ncols: usize) -> (Vec<(usize, u64)>, usize) {
    debug_assert!(ncols < RHS_BIT as usize);
    let coeff_mask: u64 = (1u64 << ncols) - 1;
    let mut pivots: Vec<(usize, u64)> = Vec::new();
    for col in 0..ncols {
        let mask = 1u64 << col;
        if let Some(i) = rows.iter().position(|&r| r & mask != 0) {
            let p = rows.swap_remove(i);
            for r in rows.iter_mut() {
                if *r & mask != 0 {
                    *r ^= p;
                }
            }
            for (_, pr) in pivots.iter_mut() {
                if *pr & mask != 0 {
                    *pr ^= p;
                }
            }
            pivots.push((col, p));
        }
    }
    let ncontra = rows
        .iter()
        .filter(|&&r| r & coeff_mask == 0 && r >> RHS_BIT == 1)
        .count();
    (pivots, ncontra)
}

/// Exact GF(2) solve of one index-group of one tensor, holding the other
/// two tensors (and frozen bits) fixed.  The Brent equations partition so
/// that every equation touches exactly one gamma-group (p,q) — likewise
/// one alpha-group (a,b) and one beta-group (c,d) — so solving a group
/// satisfies ALL of its equations, and a fully-consistent tensor closure
/// solves the whole instance.  Free (non-pivot) vars keep their current
/// values; on inconsistency bits are left untouched.
/// Returns Ok(#bits changed) or Err(#contradiction rows).
pub fn closure_group(
    d: Dims,
    bits: &mut [u8],
    frozen: &[u8],
    block: Block,
    gi: usize,
    gj: usize,
) -> Result<usize, usize> {
    let r = d.r;
    assert!(r < RHS_BIT as usize, "r too large for u64 rows");
    let var = |m: usize| -> usize {
        (match block {
            Block::Alpha => d.a_idx(m, gi, gj),
            Block::Beta => d.b_idx(m, gi, gj),
            Block::Gamma => d.g_idx(m, gi, gj),
        }) as usize
    };
    let mut rows: Vec<u64> = Vec::with_capacity(81);
    let mut push_row = |coeffs: &dyn Fn(usize) -> u8, rhs0: bool| {
        let mut row: u64 = 0;
        let mut rhs = rhs0 as u64;
        for m in 0..r {
            if coeffs(m) == 1 {
                let v = var(m);
                if frozen[v] == 1 {
                    rhs ^= bits[v] as u64;
                } else {
                    row |= 1 << m;
                }
            }
        }
        rows.push(row | (rhs << RHS_BIT));
    };
    match block {
        Block::Gamma => {
            // group (p,q)=(gi,gj); equations over (a,b,c,dd)
            for a in 0..d.n1 {
                for b in 0..d.n2 {
                    for c in 0..d.n2 {
                        for dd in 0..d.n3 {
                            push_row(
                                &|m| {
                                    bits[d.a_idx(m, a, b) as usize]
                                        & bits[d.b_idx(m, c, dd) as usize]
                                },
                                b == c && a == gi && dd == gj,
                            );
                        }
                    }
                }
            }
        }
        Block::Alpha => {
            // group (a,b)=(gi,gj); equations over (c,dd,p,q)
            for c in 0..d.n2 {
                for dd in 0..d.n3 {
                    for p in 0..d.n1 {
                        for q in 0..d.n3 {
                            push_row(
                                &|m| {
                                    bits[d.b_idx(m, c, dd) as usize]
                                        & bits[d.g_idx(m, p, q) as usize]
                                },
                                gj == c && gi == p && dd == q,
                            );
                        }
                    }
                }
            }
        }
        Block::Beta => {
            // group (c,dd)=(gi,gj); equations over (a,b,p,q)
            for a in 0..d.n1 {
                for b in 0..d.n2 {
                    for p in 0..d.n1 {
                        for q in 0..d.n3 {
                            push_row(
                                &|m| {
                                    bits[d.a_idx(m, a, b) as usize]
                                        & bits[d.g_idx(m, p, q) as usize]
                                },
                                b == gi && a == p && gj == q,
                            );
                        }
                    }
                }
            }
        }
    }
    let (pivots, ncontra) = gauss_rref(&mut rows, r);
    if ncontra > 0 {
        return Err(ncontra);
    }
    let coeff_mask: u64 = (1u64 << r) - 1;
    let mut changed = 0;
    for &(col, prow) in &pivots {
        let mut val = (prow >> RHS_BIT) & 1;
        let mut rest = prow & coeff_mask & !(1u64 << col);
        while rest != 0 {
            let c2 = rest.trailing_zeros() as usize;
            rest &= rest - 1;
            val ^= bits[var(c2)] as u64;
        }
        let v = var(col);
        if bits[v] != val as u8 {
            bits[v] = val as u8;
            changed += 1;
        }
    }
    Ok(changed)
}

/// Closure over all index-groups of one tensor.  Monotone: solved groups
/// satisfy all their equations, untouched groups are unchanged.
/// Returns (consistent groups, total contradiction rows, bits changed).
pub fn closure_tensor(
    d: Dims,
    bits: &mut [u8],
    frozen: &[u8],
    block: Block,
) -> (usize, usize, usize) {
    let (ni, nj) = match block {
        Block::Alpha => (d.n1, d.n2),
        Block::Beta => (d.n2, d.n3),
        Block::Gamma => (d.n1, d.n3),
    };
    let (mut ok, mut contra, mut changed) = (0, 0, 0);
    for gi in 0..ni {
        for gj in 0..nj {
            match closure_group(d, bits, frozen, block, gi, gj) {
                Ok(ch) => {
                    ok += 1;
                    changed += ch;
                }
                Err(nc) => contra += nc,
            }
        }
    }
    (ok, contra, changed)
}

// ---------------------------------------------------------------- sls

#[derive(Clone, Copy)]
pub struct SlsCfg {
    /// walk probability (WalkSAT) / unused for probSAT
    pub noise: f64,
    /// probSAT exponential base; policy = probSAT when `probsat`
    pub cb: f64,
    pub probsat: bool,
    /// random-init one-density for free vars
    pub density: f64,
    /// flips per Luby unit (restart schedule); 0 = no restarts
    pub luby_unit: u64,
    /// odd restarts re-start from the chain-best assignment with each free
    /// bit flipped with this probability; 0 disables (always fresh random)
    pub pert: f64,
    /// call the closure hook every this many flips; 0 disables
    pub closure_every: u64,
    pub seed: u64,
    pub max_secs: f64,
}

/// Injected "big move" (e.g. Brent tensor closure): mutates bits given the
/// frozen mask; the u64 is the invocation counter (for cycling tensors).
/// The SLS recomputes its incremental state after each call.
pub type Hook<'h> = &'h (dyn Fn(&mut [u8], &[u8], u64) + Sync);

impl Default for SlsCfg {
    fn default() -> Self {
        SlsCfg {
            noise: 0.2,
            cb: 2.5,
            probsat: false,
            density: 0.25,
            luby_unit: 1 << 20,
            pert: 0.06,
            closure_every: 0,
            seed: 1,
            max_secs: 10.0,
        }
    }
}

fn luby(mut k: u64) -> u64 {
    // standard Luby sequence, 1-indexed
    loop {
        if (k + 1).is_power_of_two() {
            return (k + 1) / 2;
        }
        let p = (u64::BITS - 1 - k.leading_zeros()) as u64; // floor log2
        k -= (1 << p) - 1;
    }
}

pub struct Sls<'a> {
    pub anf: &'a Anf,
    pub bits: Vec<u8>,
    parity: Vec<u8>,
    unsat: Vec<u32>,
    pos: Vec<u32>,
    frozen: Vec<u8>,
    frozen_val: Vec<(u32, u8)>,
    pub flips: u64,
    /// chain-best assignment (fewest unsat seen) and its unsat count
    pub best_bits: Vec<u8>,
    pub best_n: usize,
    rng: Rng,
    cands: Vec<u32>,
    pow_cb: [f64; 32],
}

const SAT_POS: u32 = u32::MAX;

impl<'a> Sls<'a> {
    pub fn new(anf: &'a Anf, frozen: &[(u32, u8)], cfg: &SlsCfg) -> Sls<'a> {
        let mut fz = vec![0u8; anf.nvars];
        for &(v, _) in frozen {
            fz[v as usize] = 1;
        }
        let mut pow_cb = [0.0; 32];
        for (b, p) in pow_cb.iter_mut().enumerate() {
            *p = cfg.cb.powi(-(b as i32));
        }
        Sls {
            anf,
            bits: vec![0; anf.nvars],
            parity: vec![0; anf.neqs()],
            unsat: Vec::new(),
            pos: vec![SAT_POS; anf.neqs()],
            frozen: fz,
            frozen_val: frozen.to_vec(),
            flips: 0,
            best_bits: Vec::new(),
            best_n: usize::MAX,
            rng: Rng::new(cfg.seed),
            cands: Vec::new(),
            pow_cb,
        }
    }

    pub fn init_random(&mut self, density: f64) {
        for v in 0..self.anf.nvars {
            self.bits[v] = (self.rng.f64() < density) as u8;
        }
        for &(v, b) in &self.frozen_val {
            self.bits[v as usize] = b;
        }
        self.recompute();
    }

    fn recompute(&mut self) {
        self.unsat.clear();
        for e in 0..self.anf.neqs() {
            let mut acc = 0u8;
            for i in self.anf.eq_off[e]..self.anf.eq_off[e + 1] {
                let [x, y, z] = self.anf.mons[i as usize];
                acc ^= self.bits[x as usize]
                    & self.bits[y as usize]
                    & self.bits[z as usize];
            }
            self.parity[e] = acc;
            if acc != self.anf.rhs[e] {
                self.pos[e] = self.unsat.len() as u32;
                self.unsat.push(e as u32);
            } else {
                self.pos[e] = SAT_POS;
            }
        }
    }

    #[inline]
    fn toggle_eq(&mut self, e: u32) {
        let eu = e as usize;
        self.parity[eu] ^= 1;
        if self.parity[eu] != self.anf.rhs[eu] {
            self.pos[eu] = self.unsat.len() as u32;
            self.unsat.push(e);
        } else {
            let i = self.pos[eu] as usize;
            let last = *self.unsat.last().unwrap();
            self.unsat[i] = last;
            self.pos[last as usize] = i as u32;
            self.unsat.pop();
            self.pos[eu] = SAT_POS;
        }
    }

    #[inline]
    pub fn flip(&mut self, v: u32) {
        let vu = v as usize;
        self.bits[vu] ^= 1;
        let (s, t) = (self.anf.adj_off[vu], self.anf.adj_off[vu + 1]);
        for i in s..t {
            let Adj { eq, p1, p2 } = self.anf.adj[i as usize];
            if self.bits[p1 as usize] & self.bits[p2 as usize] == 1 {
                self.toggle_eq(eq);
            }
        }
        self.flips += 1;
    }

    /// #equations that flipping `v` turns sat -> unsat
    #[inline]
    fn break_of(&self, v: u32) -> u32 {
        let vu = v as usize;
        let (s, t) = (self.anf.adj_off[vu], self.anf.adj_off[vu + 1]);
        let mut br = 0;
        for i in s..t {
            let Adj { eq, p1, p2 } = self.anf.adj[i as usize];
            br += (self.bits[p1 as usize] & self.bits[p2 as usize] == 1
                && self.parity[eq as usize] == self.anf.rhs[eq as usize])
                as u32;
        }
        br
    }

    /// one SLS move; `true` while unsat remains
    pub fn step(&mut self, cfg: &SlsCfg) -> bool {
        if self.unsat.is_empty() {
            return false;
        }
        let e = self.unsat[self.rng.below(self.unsat.len())] as usize;
        // toggling candidates: positions whose two partners are both 1
        self.cands.clear();
        for i in self.anf.eq_off[e]..self.anf.eq_off[e + 1] {
            let [x, y, z] = self.anf.mons[i as usize];
            let (bx, by, bz) = (
                self.bits[x as usize],
                self.bits[y as usize],
                self.bits[z as usize],
            );
            if by & bz == 1 && self.frozen[x as usize] == 0 {
                self.cands.push(x);
            }
            if bx & bz == 1 && self.frozen[y as usize] == 0 {
                self.cands.push(y);
            }
            if bx & by == 1 && self.frozen[z as usize] == 0 {
                self.cands.push(z);
            }
        }
        if self.cands.is_empty() {
            // no single flip toggles e: random walk on e's variables
            let (s, t) = (self.anf.eqv_off[e], self.anf.eqv_off[e + 1]);
            for _ in 0..8 {
                let v = self.anf.eqv[s as usize
                    + self.rng.below((t - s) as usize)];
                if self.frozen[v as usize] == 0 {
                    self.flip(v);
                    break;
                }
            }
            return !self.unsat.is_empty();
        }
        let v = if cfg.probsat {
            // probSAT: sample candidate with weight cb^-break
            let mut tot = 0.0;
            let mut ws = [0.0f64; 128];
            let ncand = self.cands.len().min(128);
            for ci in 0..ncand {
                let b = self.break_of(self.cands[ci]).min(31);
                let w = self.pow_cb[b as usize];
                ws[ci] = w;
                tot += w;
            }
            let mut x = self.rng.f64() * tot;
            let mut pick = 0;
            for (ci, w) in ws[..ncand].iter().enumerate() {
                x -= w;
                if x <= 0.0 {
                    pick = ci;
                    break;
                }
            }
            self.cands[pick]
        } else {
            // WalkSAT/SKC: freebie, else noise-random, else min-break
            let mut best = self.cands[0];
            let mut bestbr = u32::MAX;
            let mut freebie = None;
            for ci in 0..self.cands.len() {
                let v = self.cands[ci];
                let b = self.break_of(v);
                if b == 0 {
                    freebie = Some(v);
                    break;
                }
                if b < bestbr {
                    bestbr = b;
                    best = v;
                }
            }
            match freebie {
                Some(v) => v,
                None if self.rng.f64() < cfg.noise => {
                    self.cands[self.rng.below(self.cands.len())]
                }
                None => best,
            }
        };
        self.flip(v);
        !self.unsat.is_empty()
    }

    pub fn nunsat(&self) -> usize {
        self.unsat.len()
    }

    /// Luby-restart chain until solved / deadline / stop-flag.  Odd
    /// restarts resume from the chain-best assignment, perturbed (each
    /// free bit flipped w.p. `cfg.pert`); even restarts are fresh random.
    /// Returns true when solved (bits hold the solution).
    pub fn run(
        &mut self,
        cfg: &SlsCfg,
        t0: Instant,
        stop: &AtomicBool,
        best_seen: &mut usize,
        hook: Option<Hook>,
    ) -> bool {
        let mut restart = 1u64;
        let mut next_hook = cfg.closure_every;
        let mut hook_k = 0u64;
        loop {
            if cfg.pert > 0.0 && restart % 2 == 0 && !self.best_bits.is_empty()
            {
                let bb = std::mem::take(&mut self.best_bits);
                self.bits.copy_from_slice(&bb);
                self.best_bits = bb;
                for v in 0..self.anf.nvars {
                    if self.frozen[v] == 0 && self.rng.f64() < cfg.pert {
                        self.bits[v] ^= 1;
                    }
                }
                self.recompute();
            } else {
                self.init_random(cfg.density);
            }
            if self.unsat.is_empty() {
                return true;
            }
            let budget = if cfg.luby_unit == 0 {
                u64::MAX
            } else {
                luby(restart).saturating_mul(cfg.luby_unit)
            };
            let mut left = budget;
            loop {
                if !self.step(cfg) {
                    return self.unsat.is_empty();
                }
                if let Some(h) = hook {
                    if cfg.closure_every > 0 && self.flips >= next_hook {
                        h(&mut self.bits, &self.frozen, hook_k);
                        hook_k += 1;
                        next_hook = self.flips + cfg.closure_every;
                        self.recompute();
                        if self.unsat.is_empty() {
                            return true;
                        }
                    }
                }
                if self.unsat.len() < self.best_n {
                    self.best_n = self.unsat.len();
                    let mut bb = std::mem::take(&mut self.best_bits);
                    bb.clear();
                    bb.extend_from_slice(&self.bits);
                    self.best_bits = bb;
                    *best_seen = (*best_seen).min(self.best_n);
                }
                left -= 1;
                if left == 0 {
                    break;
                }
                if self.flips % 4096 == 0
                    && (stop.load(Ordering::Relaxed)
                        || t0.elapsed().as_secs_f64() > cfg.max_secs)
                {
                    return false;
                }
            }
            restart += 1;
        }
    }
}

/// Portfolio: `threads` independent Luby chains (seeds `cfg.seed + i`),
/// first solution wins.  Returns (solution bits, total flips, best unsat
/// seen, best-assignment bits across chains — empty when solved).
pub fn solve_portfolio(
    anf: &Anf,
    frozen: &[(u32, u8)],
    cfg: &SlsCfg,
    threads: usize,
    hook: Option<Hook>,
) -> (Option<Vec<u8>>, u64, usize, Vec<u8>) {
    let stop = AtomicBool::new(false);
    let t0 = Instant::now();
    let results: Vec<(Option<Vec<u8>>, u64, usize, Vec<u8>)> = (0..threads)
        .into_par_iter()
        .map(|i| {
            let mut c = *cfg;
            c.seed = cfg.seed.wrapping_add(i as u64).wrapping_mul(0x9e37);
            let mut sls = Sls::new(anf, frozen, &c);
            let mut best = usize::MAX;
            let ok = sls.run(&c, t0, &stop, &mut best, hook);
            if ok {
                stop.store(true, Ordering::Relaxed);
                (Some(sls.bits.clone()), sls.flips, 0, Vec::new())
            } else {
                (None, sls.flips, best, std::mem::take(&mut sls.best_bits))
            }
        })
        .collect();
    let mut flips = 0;
    let mut best = usize::MAX;
    let mut sol = None;
    let mut best_bits = Vec::new();
    for (s, f, b, bb) in results {
        flips += f;
        if b < best {
            best = b;
            best_bits = bb;
        }
        if s.is_some() && sol.is_none() {
            sol = s;
        }
    }
    if sol.is_some() {
        best_bits.clear();
    }
    (sol, flips, best, best_bits)
}

// ---------------------------------------------------------------- tests

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn schemes_verify() {
        let d3 = Dims { n1: 3, n2: 3, n3: 3, r: 23 };
        let anf = brent(d3);
        assert_eq!(anf.nvars, 621);
        assert_eq!(anf.neqs(), 729);
        assert_eq!(anf.rhs.iter().map(|&x| x as usize).sum::<usize>(), 27);
        let lb = bits_of(LADERMAN_BITS);
        assert_eq!(lb.len(), 621);
        assert_eq!(verify(&anf, &lb), 0, "laderman must satisfy brent");

        let d2 = Dims { n1: 2, n2: 2, n3: 2, r: 7 };
        let anf2 = brent(d2);
        let sb = bits_of(STRASSEN_BITS);
        assert_eq!(verify(&anf2, &sb), 0, "strassen must satisfy brent");
        // sensitivity: any single flip breaks it
        let mut b = sb.clone();
        for v in 0..b.len() {
            b[v] ^= 1;
            assert!(verify(&anf2, &b) > 0);
            b[v] ^= 1;
        }
    }

    #[test]
    fn incremental_matches_scratch() {
        let d = Dims { n1: 2, n2: 2, n3: 2, r: 7 };
        let anf = brent(d);
        let cfg = SlsCfg { seed: 7, ..Default::default() };
        let mut s = Sls::new(&anf, &[], &cfg);
        s.init_random(0.5);
        for i in 0..10_000 {
            let v = (i * 37) % anf.nvars;
            s.flip(v as u32);
            if i % 1000 == 0 {
                assert_eq!(s.nunsat(), verify(&anf, &s.bits));
            }
        }
        assert_eq!(s.nunsat(), verify(&anf, &s.bits));
    }

    #[test]
    fn solves_strassen_size() {
        let d = Dims { n1: 2, n2: 2, n3: 2, r: 7 };
        let anf = brent(d);
        let cfg = SlsCfg { max_secs: 30.0, seed: 3, ..Default::default() };
        let (sol, _, _, _) = solve_portfolio(&anf, &[], &cfg, 1, None);
        let bits = sol.expect("2x2x2 r=7 should solve fast");
        assert_eq!(verify(&anf, &bits), 0);
    }

    #[test]
    fn closure_reconstructs_each_tensor() {
        let d = Dims { n1: 3, n2: 3, n3: 3, r: 23 };
        let anf = brent(d);
        let lb = bits_of(LADERMAN_BITS);
        let nofrz = vec![0u8; anf.nvars];
        for (block, lo, hi) in [
            (Block::Gamma, 414, 621),
            (Block::Alpha, 0, 207),
            (Block::Beta, 207, 414),
        ] {
            let mut bits = lb.clone();
            for v in lo..hi {
                bits[v] = 0; // wipe the tensor entirely
            }
            let (ok, contra, changed) =
                closure_tensor(d, &mut bits, &nofrz, block);
            assert_eq!(ok, 9, "{block:?}: all 9 groups must be consistent");
            assert_eq!(contra, 0);
            assert!(changed > 0);
            assert_eq!(verify(&anf, &bits), 0,
                "{block:?}-closure must yield a full valid scheme");
        }
    }

    #[test]
    fn closure_respects_frozen_and_is_monotone() {
        let d = Dims { n1: 3, n2: 3, n3: 3, r: 23 };
        let anf = brent(d);
        let lb = bits_of(LADERMAN_BITS);
        // freeze all gamma bits at laderman, wipe the rest, random alpha/beta
        let mut rng = Rng::new(99);
        let mut bits: Vec<u8> =
            (0..anf.nvars).map(|_| (rng.f64() < 0.25) as u8).collect();
        let mut frozen = vec![0u8; anf.nvars];
        for v in 414..621 {
            bits[v] = lb[v];
            frozen[v] = 1;
        }
        let before = verify(&anf, &bits);
        let snapshot: Vec<u8> = bits[414..621].to_vec();
        let (_, _, _) = closure_tensor(d, &mut bits, &frozen, Block::Gamma);
        assert_eq!(&bits[414..621], &snapshot[..], "frozen bits must not move");
        // monotone: gamma-closure never increases violations
        let (_, _, _) = closure_tensor(d, &mut bits, &vec![0u8; anf.nvars],
            Block::Gamma);
        assert!(verify(&anf, &bits) <= before);
    }

    #[test]
    fn seeded_repair_laderman() {
        let d = Dims { n1: 3, n2: 3, n3: 3, r: 23 };
        let anf = brent(d);
        let lb = bits_of(LADERMAN_BITS);
        let mut rng = Rng::new(11);
        // fix 414 random bits at laderman values
        let mut idx: Vec<u32> = (0..621).collect();
        for i in (1..idx.len()).rev() {
            idx.swap(i, rng.below(i + 1));
        }
        let frozen: Vec<(u32, u8)> =
            idx[..414].iter().map(|&v| (v, lb[v as usize])).collect();
        let cfg = SlsCfg { max_secs: 30.0, seed: 5, ..Default::default() };
        let (sol, flips, _, _) = solve_portfolio(&anf, &frozen, &cfg, 1, None);
        let bits = sol.expect("414-seeded repair should solve");
        assert_eq!(verify(&anf, &bits), 0);
        assert!(flips < 5_000_000, "repair took {flips} flips");
    }

    #[test]
    fn pairing_generates() {
        let d = Dims { n1: 3, n2: 3, n3: 3, r: 23 };
        let mut rng = Rng::new(1);
        let mut ok = 0;
        for _ in 0..20 {
            if let Some(fr) = random_pairing(d, &mut rng) {
                assert_eq!(fr.len(), 81);
                ok += 1;
            }
        }
        assert!(ok > 0);
    }
}
