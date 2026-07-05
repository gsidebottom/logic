//! Orbit-wide GF(2) side-cost floors for 3x3x23 matrix-multiplication
//! schemes — the Rust port of `matmul/orbitscan.py`'s table machinery.
//!
//! The de Groote sandwich (P A Q^-1, Q B R^-1, R C~ P^-1) factors by
//! side: the A-form multiset depends only on (P,Q), B on (Q,R), C on
//! (R,P).  Three 168x168 tables of exact GF(2) side costs therefore
//! cover an entire orbit (168^3 sandwiches per S3 slot variant).  A
//! GF(2) side cost lower-bounds the Z side cost of the same
//! representative (reduce any Z-chain mod 2), so table minima give
//! sound orbit-wide side floors.
//!
//! The exact GF(2) side cost is addition-chain covering over XOR:
//! minimum #steps v = x XOR y (x, y earlier values, from the 9 basis
//! vectors) such that every distinct row of weight >= 2 appears among
//! the values.  Solved by iterative deepening on the number of helper
//! values with a closure normal form (complete by an exchange
//! argument — see matmul/sidemin.py for the signed-Z version and the
//! calibration against Sun's optimality certificates).

use std::collections::{HashMap, HashSet};

pub const NG: usize = 168;
const NA: usize = 207; // 23 * 9
const NB: usize = 207;

// ---------------- GF(2) 3x3 matrices as 9-bit ints ----------------
// bit (3*i + j) = entry (row i, col j); identity = 0b100010001.

pub fn mat_get(m: u16, i: usize, j: usize) -> u16 {
    (m >> (3 * i + j)) & 1
}

pub fn mat_mul(a: u16, b: u16) -> u16 {
    let mut c = 0u16;
    for i in 0..3 {
        for j in 0..3 {
            let mut v = 0u16;
            for k in 0..3 {
                v ^= mat_get(a, i, k) & mat_get(b, k, j);
            }
            c |= v << (3 * i + j);
        }
    }
    c
}

pub fn mat_transpose(m: u16) -> u16 {
    let mut t = 0u16;
    for i in 0..3 {
        for j in 0..3 {
            if mat_get(m, i, j) == 1 {
                t |= 1 << (3 * j + i);
            }
        }
    }
    t
}

pub fn mat_inv(m: u16) -> Option<u16> {
    let mut a = [(m & 7), (m >> 3) & 7, (m >> 6) & 7];
    let mut b = [1u16, 2, 4]; // identity rows, column j at bit j
    for col in 0..3 {
        let bit = 1u16 << col;
        let piv = (col..3).find(|&k| a[k] & bit != 0)?;
        a.swap(col, piv);
        b.swap(col, piv);
        for k in 0..3 {
            if k != col && a[k] & bit != 0 {
                a[k] ^= a[col];
                b[k] ^= b[col];
            }
        }
    }
    Some(b[0] | (b[1] << 3) | (b[2] << 6))
}

/// all 168 invertible 3x3 GF(2) matrices, ascending.
pub fn gl3() -> Vec<u16> {
    (0u16..512).filter(|&m| mat_inv(m).is_some()).collect()
}

// ---------------- scheme I/O ----------------

/// 621-bit brent-order vector -> 23 summands (A, B, C~ = gamma^T).
pub fn bits_to_summands(bits: &[u8]) -> Vec<(u16, u16, u16)> {
    assert_eq!(bits.len(), 621);
    (0..23)
        .map(|m| {
            let (mut a, mut b, mut g) = (0u16, 0u16, 0u16);
            for k in 0..9 {
                if bits[m * 9 + k] == 1 {
                    a |= 1 << k;
                }
                if bits[NA + m * 9 + k] == 1 {
                    b |= 1 << k;
                }
                if bits[NA + NB + m * 9 + k] == 1 {
                    g |= 1 << k;
                }
            }
            (a, b, mat_transpose(g))
        })
        .collect()
}

/// Brent equations mod 2 over the summand form; returns #violated (0 = valid).
pub fn brent_bad(summands: &[(u16, u16, u16)]) -> usize {
    let mut bad = 0;
    for i in 0..3 {
        for l in 0..3 {
            for lp in 0..3 {
                for j in 0..3 {
                    for ip in 0..3 {
                        for jp in 0..3 {
                            let mut s = 0u16;
                            for &(a, b, ct) in summands {
                                // gamma[ip][jp] = C~[jp][ip]
                                s ^= mat_get(a, i, l)
                                    & mat_get(b, lp, j)
                                    & mat_get(ct, jp, ip);
                            }
                            let rhs =
                                u16::from(l == lp && i == ip && j == jp);
                            if s != rhs {
                                bad += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    bad
}

/// the 6 S3 slot variants, same order as matmul/equiv.py: identity,
/// cyc, cyc^2, swp, swp*cyc, swp*cyc^2.
pub fn s3_variants(sm: &[(u16, u16, u16)]) -> Vec<Vec<(u16, u16, u16)>> {
    let cyc = |ss: &[(u16, u16, u16)]| -> Vec<(u16, u16, u16)> {
        ss.iter().map(|&(a, b, c)| (b, c, a)).collect()
    };
    let swp: Vec<(u16, u16, u16)> = sm
        .iter()
        .map(|&(a, b, c)| {
            (mat_transpose(b), mat_transpose(a), mat_transpose(c))
        })
        .collect();
    let mut v = vec![sm.to_vec()];
    v.push(cyc(&v[0]));
    v.push(cyc(&v[1]));
    v.push(swp);
    v.push(cyc(&v[3]));
    v.push(cyc(&v[4]));
    v
}

// ---------------- exact GF(2) side cost ----------------

/// 512-bit membership set over 9-bit values.
#[derive(Clone, PartialEq, Eq, Hash)]
struct Pool([u64; 8]);

impl Pool {
    fn new() -> Self {
        Pool([0; 8])
    }
    #[inline]
    fn has(&self, v: u16) -> bool {
        self.0[(v >> 6) as usize] >> (v & 63) & 1 == 1
    }
    #[inline]
    fn add(&mut self, v: u16) {
        self.0[(v >> 6) as usize] |= 1 << (v & 63);
    }
}

pub struct SideCost {
    pub adds: u32,
    /// false = node cap hit; `adds` is then a valid LOWER bound.
    pub exact: bool,
    pub nodes: u64,
}

struct Search {
    targets: Vec<u16>,
    nodes: u64,
    node_cap: u64,
}

impl Search {
    /// cover every derivable target (pool only grows => greedy cover
    /// is safe); returns updated uncovered mask.
    fn close(&self, pool: &mut Pool, list: &mut Vec<u16>, mut unc: u32) -> u32 {
        let mut progress = true;
        while progress {
            progress = false;
            let mut m = unc;
            while m != 0 {
                let ti = m.trailing_zeros() as usize;
                m &= m - 1;
                let t = self.targets[ti];
                if list.iter().any(|&x| pool.has(t ^ x)) {
                    pool.add(t);
                    list.push(t);
                    unc &= !(1 << ti);
                    progress = true;
                }
            }
        }
        unc
    }

    fn dfs(
        &mut self,
        mut pool: Pool,
        mut list: Vec<u16>,
        unc0: u32,
        h: u32,
        memo: &mut Vec<HashSet<Pool>>,
    ) -> Result<bool, ()> {
        self.nodes += 1;
        if self.nodes > self.node_cap {
            return Err(());
        }
        let unc = self.close(&mut pool, &mut list, unc0);
        if unc == 0 {
            return Ok(true);
        }
        if h == 0 {
            return Ok(false);
        }
        if !memo[h as usize].insert(pool.clone()) {
            return Ok(false);
        }
        // enabling counts: u completes target t as t = x XOR u
        let mut enab: HashMap<u16, u32> = HashMap::new();
        let mut m = unc;
        while m != 0 {
            let ti = m.trailing_zeros() as usize;
            m &= m - 1;
            let t = self.targets[ti];
            for &x in &list {
                let u = t ^ x;
                if !pool.has(u) {
                    *enab.entry(u).or_insert(0) += 1;
                }
            }
        }
        let mut cands: Vec<u16> = if h == 1 {
            // last helper must directly complete some target, and must
            // itself be creatable from the pool
            enab.keys()
                .copied()
                .filter(|&u| list.iter().any(|&x| pool.has(u ^ x)))
                .collect()
        } else {
            let mut set = HashSet::new();
            for i in 0..list.len() {
                for j in 0..i {
                    let v = list[i] ^ list[j];
                    if v != 0 && !pool.has(v) {
                        set.insert(v);
                    }
                }
            }
            set.into_iter().collect()
        };
        cands.sort_by_key(|&u| {
            (
                std::cmp::Reverse(enab.get(&u).copied().unwrap_or(0)),
                u.count_ones(),
                u,
            )
        });
        for u in cands {
            let mut p2 = pool.clone();
            let mut l2 = list.clone();
            p2.add(u);
            l2.push(u);
            if self.dfs(p2, l2, unc, h - 1, memo)? {
                return Ok(true);
            }
        }
        Ok(false)
    }
}

/// exact minimum XOR-chain additions covering all weight>=2 rows.
pub fn gf2_min_side(rows: &[u16], max_slack: u32, node_cap: u64) -> SideCost {
    let mut targets: Vec<u16> = Vec::new();
    for &r in rows {
        if r.count_ones() >= 2 && !targets.contains(&r) {
            targets.push(r);
        }
    }
    let nt = targets.len() as u32;
    if nt == 0 {
        return SideCost { adds: 0, exact: true, nodes: 0 };
    }
    assert!(targets.len() <= 32, "uncovered mask is u32");
    let mut s = Search { targets, nodes: 0, node_cap };
    let full: u32 = if s.targets.len() == 32 {
        u32::MAX
    } else {
        (1u32 << s.targets.len()) - 1
    };
    for h in 0..=max_slack {
        let mut memo: Vec<HashSet<Pool>> =
            (0..=h).map(|_| HashSet::new()).collect();
        let mut pool = Pool::new();
        let mut list = Vec::with_capacity(40);
        for i in 0..9u16 {
            pool.add(1 << i);
            list.push(1 << i);
        }
        match s.dfs(pool, list, full, h, &mut memo) {
            Ok(true) => {
                return SideCost { adds: nt + h, exact: true, nodes: s.nodes }
            }
            Ok(false) => {}
            // levels < h exhausted => nt + h is a sound lower bound
            Err(()) => {
                return SideCost { adds: nt + h, exact: false, nodes: s.nodes }
            }
        }
    }
    SideCost { adds: nt + max_slack + 1, exact: false, nodes: s.nodes }
}

// ---------------- greedy GF(2) C estimate ----------------

/// 9 output forms over the 23 products (bits 0..22; aux symbols get
/// bits 23+).  Greedy pair extraction; an ESTIMATE, not a bound.
/// Tie-break = first pair reaching the max count in insertion order —
/// bit-for-bit the same trajectory as the Python reference
/// (CPython dict + max()), so table estimates match orbitscan.py.
pub fn gf2_c_greedy(forms0: &[u64; 9]) -> u32 {
    let mut forms: Vec<u64> = forms0.to_vec();
    let mut next_aux = 23u32;
    let mut adds = 0u32;
    loop {
        let mut order: Vec<u64> = Vec::new();
        let mut counts: HashMap<u64, u32> = HashMap::new();
        for &f in &forms {
            let mut bits: Vec<u64> = Vec::with_capacity(24);
            let mut x = f;
            while x != 0 {
                let b = x & x.wrapping_neg();
                bits.push(b);
                x ^= b;
            }
            for i in 0..bits.len() {
                for j in 0..i {
                    let key = bits[i] | bits[j];
                    let e = counts.entry(key).or_insert(0);
                    if *e == 0 {
                        order.push(key);
                    }
                    *e += 1;
                }
            }
        }
        let mut best: Option<(u64, u32)> = None;
        for &key in &order {
            let k = counts[&key];
            if best.map_or(true, |(_, bk)| k > bk) {
                best = Some((key, k));
            }
        }
        match best {
            Some((pair, k)) if k >= 2 => {
                let w = 1u64 << next_aux;
                next_aux += 1;
                adds += 1;
                for f in forms.iter_mut() {
                    if *f & pair == pair {
                        *f = (*f ^ pair) | w;
                    }
                }
            }
            _ => break,
        }
    }
    adds + forms
        .iter()
        .map(|f| f.count_ones().max(1) - 1)
        .sum::<u32>()
}

// ---------------- tables + scan ----------------

pub struct Tables {
    /// row-major NG x NG: a[p*NG+q], b[q*NG+r], c[r*NG+p]
    pub a: Vec<u16>,
    pub b: Vec<u16>,
    pub c: Vec<u16>,
    /// cells where the side search was inexact — max-slack exhausted
    /// (true cost >= nt + max_slack + 1, the stored value) or, in
    /// principle, node-cap hit.  Entries are LOWER bounds either way,
    /// so floors stay sound; the Python reference stores the same
    /// values silently.
    pub open_cells: usize,
}

/// distinct weight>=2 rows — a sound lower bound on the side cost,
/// ~100x cheaper than the exact search.
pub fn gf2_nt(rows: &[u16]) -> u32 {
    let mut seen = [false; 512];
    let mut nt = 0u32;
    for &r in rows {
        if r.count_ones() >= 2 && !seen[r as usize] {
            seen[r as usize] = true;
            nt += 1;
        }
    }
    nt
}

/// build the three side-cost tables for one variant.  `with_c` off
/// skips the C table (floors need A and B only).  `screen_nt`: cells
/// whose distinct-target count exceeds it store nt — a sound lower
/// bound, so screened floors are lower bounds and no class whose
/// true floor is under a hunt cutoff can be missed (verify
/// survivors with an exact pass).
pub fn side_tables(
    sm: &[(u16, u16, u16)],
    gl: &[u16],
    max_slack: u32,
    node_cap: u64,
    with_c: bool,
) -> Tables {
    side_tables_screened(sm, gl, max_slack, node_cap, with_c, None)
}

pub fn side_tables_screened(
    sm: &[(u16, u16, u16)],
    gl: &[u16],
    max_slack: u32,
    node_cap: u64,
    with_c: bool,
    screen_nt: Option<u32>,
) -> Tables {
    use rayon::prelude::*;
    let gli: Vec<u16> = gl.iter().map(|&g| mat_inv(g).unwrap()).collect();
    let amats: Vec<u16> = sm.iter().map(|s| s.0).collect();
    let bmats: Vec<u16> = sm.iter().map(|s| s.1).collect();
    let cmats: Vec<u16> = sm.iter().map(|s| s.2).collect();
    let cost = |rows9: &[u16], over: &mut usize| -> u16 {
        if let Some(t) = screen_nt {
            let nt = gf2_nt(rows9);
            if nt > t {
                return nt as u16; // sound lower bound, search skipped
            }
        }
        let sc = gf2_min_side(rows9, max_slack, node_cap);
        *over += usize::from(!sc.exact);
        sc.adds as u16
    };
    let rows: Vec<(Vec<u16>, Vec<u16>, Vec<u16>, usize)> = (0..NG)
        .into_par_iter()
        .map(|li| {
            let l = gl[li];
            let la: Vec<u16> = amats.iter().map(|&m| mat_mul(l, m)).collect();
            let lb: Vec<u16> = bmats.iter().map(|&m| mat_mul(l, m)).collect();
            let lc: Vec<u16> = cmats.iter().map(|&m| mat_mul(l, m)).collect();
            let mut ra = vec![0u16; NG];
            let mut rb = vec![0u16; NG];
            let mut rc = vec![0u16; NG];
            let mut over = 0usize;
            let mut rows9 = vec![0u16; 23];
            for ri in 0..NG {
                let inv = gli[ri];
                for (k, &m) in la.iter().enumerate() {
                    rows9[k] = mat_mul(m, inv);
                }
                ra[ri] = cost(&rows9, &mut over);
                for (k, &m) in lb.iter().enumerate() {
                    rows9[k] = mat_mul(m, inv);
                }
                rb[ri] = cost(&rows9, &mut over);
                if with_c {
                    let mut forms = [0u64; 9];
                    for (m, &g) in lc.iter().enumerate() {
                        let gm = mat_mul(g, inv);
                        for j in 0..9 {
                            if gm >> j & 1 == 1 {
                                forms[j] |= 1 << m;
                            }
                        }
                    }
                    rc[ri] = gf2_c_greedy(&forms) as u16;
                }
            }
            (ra, rb, rc, over)
        })
        .collect();
    let mut t = Tables {
        a: vec![0; NG * NG],
        b: vec![0; NG * NG],
        c: vec![0; NG * NG],
        open_cells: 0,
    };
    for (li, (ra, rb, rc, over)) in rows.into_iter().enumerate() {
        t.a[li * NG..(li + 1) * NG].copy_from_slice(&ra);
        t.b[li * NG..(li + 1) * NG].copy_from_slice(&rb);
        t.c[li * NG..(li + 1) * NG].copy_from_slice(&rc);
        t.open_cells += over;
    }
    t
}

pub struct ScanResult {
    /// orbit-wide lower bound on A+B side additions (sound)
    pub floor_sides: u32,
    /// min over (P,Q,R) of A+B+C_est (estimate)
    pub best_est: u32,
    /// (est, p, q, r) with est <= cutoff, ascending
    pub cands: Vec<(u32, u16, u16, u16)>,
}

pub fn scan(t: &Tables, cutoff: u32) -> ScanResult {
    let mut floor_sides = u32::MAX;
    for q in 0..NG {
        let min_a = (0..NG).map(|p| t.a[p * NG + q] as u32).min().unwrap();
        let min_b = (0..NG).map(|r| t.b[q * NG + r] as u32).min().unwrap();
        floor_sides = floor_sides.min(min_a + min_b);
    }
    let mut best_est = u32::MAX;
    let mut cands = Vec::new();
    for q in 0..NG {
        for p in 0..NG {
            let base = t.a[p * NG + q] as u32;
            for r in 0..NG {
                let est = base + t.b[q * NG + r] as u32 + t.c[r * NG + p] as u32;
                best_est = best_est.min(est);
                if est <= cutoff {
                    cands.push((est, p as u16, q as u16, r as u16));
                }
            }
        }
    }
    cands.sort_unstable();
    ScanResult { floor_sides, best_est, cands }
}

/// apply sandwich (p_i, q_i, r_i are GL indices) to a variant's summands.
pub fn apply_pqr(
    sm: &[(u16, u16, u16)],
    gl: &[u16],
    p: usize,
    q: usize,
    r: usize,
) -> Vec<(u16, u16, u16)> {
    let (gp, gq, gr) = (gl[p], gl[q], gl[r]);
    let (qi, ri, pi) =
        (mat_inv(gq).unwrap(), mat_inv(gr).unwrap(), mat_inv(gp).unwrap());
    sm.iter()
        .map(|&(a, b, c)| {
            (
                mat_mul(mat_mul(gp, a), qi),
                mat_mul(mat_mul(gq, b), ri),
                mat_mul(mat_mul(gr, c), pi),
            )
        })
        .collect()
}

/// summands -> 621-bit vector (inverse of bits_to_summands).
pub fn summands_to_bits(sm: &[(u16, u16, u16)]) -> Vec<u8> {
    let mut bits = vec![0u8; 621];
    for (m, &(a, b, ct)) in sm.iter().enumerate() {
        let g = mat_transpose(ct);
        for k in 0..9 {
            bits[m * 9 + k] = (a >> k & 1) as u8;
            bits[NA + m * 9 + k] = (b >> k & 1) as u8;
            bits[NA + NB + m * 9 + k] = (g >> k & 1) as u8;
        }
    }
    bits
}

// ---------------- tests ----------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn gl3_is_168_with_inverses() {
        let gl = gl3();
        assert_eq!(gl.len(), 168);
        let ident = 0b100_010_001u16;
        for &g in &gl {
            let gi = mat_inv(g).unwrap();
            assert_eq!(mat_mul(g, gi), ident);
            assert_eq!(mat_mul(gi, g), ident);
        }
        // (A*B)^T = B^T * A^T on a sample
        let (a, b) = (gl[17], gl[95]);
        assert_eq!(
            mat_transpose(mat_mul(a, b)),
            mat_mul(mat_transpose(b), mat_transpose(a))
        );
    }

    #[test]
    fn micro_side_optima() {
        // {e0+e1} -> 1;  {e0+e1, e0+e1+e2} -> 2;  {e0+e1+e2} -> 2 (h=1);
        // {weight-4} -> 3 (h=2);  3-target pure chain -> 3 (h=0)
        let cases: Vec<(Vec<u16>, u32)> = vec![
            (vec![0b011], 1),
            (vec![0b011, 0b111], 2),
            (vec![0b111], 2),
            (vec![0b1111], 3),
            (vec![0b011, 0b110, 0b101], 3),
        ];
        for (rows, want) in cases {
            let sc = gf2_min_side(&rows, 3, 1_000_000);
            assert!(sc.exact);
            assert_eq!(sc.adds, want, "rows {rows:?}");
        }
        // duplicates and weight-1 rows are free
        let sc = gf2_min_side(&[0b011, 0b011, 0b100, 0], 3, 1_000_000);
        assert!(sc.exact && sc.adds == 1);
    }

    fn load_sun56() -> Vec<(u16, u16, u16)> {
        let path = concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/matmul/perminov_cache/bits/sun56.bits"
        );
        let s = std::fs::read_to_string(path).unwrap();
        let tok = s.split_whitespace().last().unwrap();
        let bits: Vec<u8> =
            tok.chars().map(|c| (c as u8) - b'0').collect();
        bits_to_summands(&bits)
    }

    #[test]
    fn sun56_identity_sides_are_13() {
        let sm = load_sun56();
        assert_eq!(brent_bad(&sm), 0, "sun56 must satisfy Brent mod 2");
        let arows: Vec<u16> = sm.iter().map(|s| s.0).collect();
        let brows: Vec<u16> = sm.iter().map(|s| s.1).collect();
        let a = gf2_min_side(&arows, 3, 10_000_000);
        let b = gf2_min_side(&brows, 3, 10_000_000);
        assert!(a.exact && b.exact);
        assert_eq!((a.adds, b.adds), (13, 13));
        // variants preserve Brent validity
        for v in s3_variants(&sm) {
            assert_eq!(brent_bad(&v), 0);
        }
        // bits round-trip
        let rt = bits_to_summands(&summands_to_bits(&sm));
        assert_eq!(rt, sm);
    }

    #[test]
    #[ignore] // release-mode benchmark gate: full v0 tables + scan
    fn sun56_v0_floor_is_26() {
        let sm = load_sun56();
        let gl = gl3();
        let t = side_tables(&sm, &gl, 3, 10_000_000, true);
        assert_eq!(t.open_cells, 0);
        let r = scan(&t, 57);
        assert_eq!(r.floor_sides, 26);
        assert_eq!(r.best_est, 56);
        assert_eq!(r.cands.len(), 432);
    }
}
