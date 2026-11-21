//! kronkill: coordinate projections of a matrix multiplication scheme followed by the 2-reduction pivot search,
//! modulo the prime 1048573 (a screen).  Rust port of matmul/tomar_line/proj/kron_proj_multi.py with
//! kron_kill.py, kron_chain.py and kron_fast.py.
//!
//! Prior art: 2-reducibility is LITA's (Khoruzhii, Serafin, Gelss, Pokutta, github.com/khoruzhii/lita), a
//! generalisation of the Kauers-Moosbauer reducibility.  What this program adds is only the search over WHICH
//! products a reduction drops (an exchange walk on the pivot set, see kron_kill.py's docstring).
//!
//! In direction d the scheme is sum_t K_t (x) f_t with K_t the Kronecker product of the two other factors.  The
//! dependencies of the K_t are the null space of the Gram matrix G = (X_r X_r^T) o (X_c X_c^T); every pivot set
//! J (k products whose dependencies are independent) gives a reduced scheme, and the walk looks for the J that
//! leaves the most rows of the new slot-d factor zero.
//!
//! usage: kronkill SCHEME.json SEQS [--walk W] [--restarts R] [--threads T] [--seed S] [--mode each|end]
//!                 [--status STATUS.json] [--bar SHAPE=RANK,...] [--out OUT.csv] [--paths DIR] [--all-paths]
//!                 [--brent T]
//! SEQS: deletion sequences separated by ';' (a sequence is I3,J0,...: slot I/J/K and an index OF THE CURRENT
//! scheme), or next:PREFIX (every one-more deletion after PREFIX), or pairs, or '.' (no deletion: reduce the
//! scheme as it is).  A path file holds, per stage, the deletion, then per reduction step the direction, the
//! pivots (indices into the scheme at that step, whose product order is the exact projection's order, so
//! kron_reduce.py --pivots replays a one-step stage exactly over Q), the support of the dependencies (the
//! products an exact replay has to look at, read by src/bin/kronexact.rs) and the other products that vanish.
//! The final scheme of every sequence is checked modulo p on random matrices (--brent trials, default 3).

use rayon::prelude::*;
use serde_json::{Value, json};
use std::collections::HashMap;
use std::io::Write;
use std::sync::OnceLock;
use std::time::Instant;

const P: u64 = 1_048_573;
const RC: [(usize, usize); 3] = [(1, 2), (0, 2), (0, 1)];

static INV: OnceLock<Vec<u32>> = OnceLock::new();

fn inv_table() -> &'static Vec<u32> {
    INV.get_or_init(|| {
        let p = P as usize;
        let mut t = vec![0u32; p];
        t[1] = 1;
        for i in 2..p {
            t[i] = ((P - (P / i as u64) * t[p % i] as u64 % P) % P) as u32;
        }
        t
    })
}

#[inline]
fn inv(x: u64) -> u64 {
    debug_assert!(x % P != 0);
    inv_table()[(x % P) as usize] as u64
}

// ---------------------------------------------------------------- random numbers (splitmix64)

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Rng(seed ^ 0x9E37_79B9_7F4A_7C15)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: u64) -> u64 {
        ((self.next() >> 11) as u128 * n as u128 >> 53) as u64
    }
    fn field(&mut self) -> u64 {
        1 + self.below(P - 1)
    }
}

fn hash_str(s: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    h
}

// ---------------------------------------------------------------- schemes modulo p

#[derive(Clone)]
struct Scheme {
    n: [usize; 3],
    m: usize,
    x: [Vec<u32>; 3], // row-major, m rows of cols(s) entries
}

impl Scheme {
    fn cols(&self, s: usize) -> usize {
        cols_of(self.n, s)
    }
    fn row(&self, s: usize, t: usize) -> &[u32] {
        let c = self.cols(s);
        &self.x[s][t * c..(t + 1) * c]
    }
}

fn cols_of(n: [usize; 3], s: usize) -> usize {
    match s {
        0 => n[0] * n[1],
        1 => n[1] * n[2],
        _ => n[2] * n[0],
    }
}

/// A decimal or integer string (sign, digits, optional point) as (numerator, denominator) modulo p.
fn parse_dec(s: &str) -> (u64, u64) {
    let s = s.trim();
    let (neg, body) = match s.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, s.strip_prefix('+').unwrap_or(s)),
    };
    let (mut num, mut den, mut frac) = (0u64, 1u64, false);
    for ch in body.chars() {
        match ch {
            '0'..='9' => {
                num = (num * 10 + ch as u64 - '0' as u64) % P;
                if frac {
                    den = den * 10 % P;
                }
            }
            '.' => frac = true,
            ' ' => {}
            _ => panic!("cannot parse the entry {s:?}"),
        }
    }
    (if neg { (P - num) % P } else { num }, den)
}

fn entry_mod(v: &Value) -> u64 {
    let s = match v {
        Value::Number(x) => x.to_string(),
        Value::String(x) => x.clone(),
        _ => panic!("unexpected entry {v}"),
    };
    let mut parts = s.split('/');
    let (a, b) = parse_dec(parts.next().unwrap());
    let (c, d) = match parts.next() {
        Some(q) => parse_dec(q),
        None => (1, 1),
    };
    // (a / b) / (c / d) = a d / (b c)
    let num = a * d % P;
    let den = b * c % P;
    assert!(den != 0, "a denominator is divisible by {P}: {s}");
    num * inv(den) % P
}

fn load(path: &str) -> Scheme {
    let d: Value = serde_json::from_str(&std::fs::read_to_string(path).expect("read the scheme")).expect("JSON");
    let n: Vec<usize> = d["n"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as usize).collect();
    let n = [n[0], n[1], n[2]];
    let m = d["m"].as_u64().unwrap() as usize;
    let mut x: [Vec<u32>; 3] = [vec![], vec![], vec![]];
    for (s, key) in ["u", "v", "w"].iter().enumerate() {
        let rows = d[*key].as_array().unwrap();
        assert_eq!(rows.len(), m, "{key} has {} rows, m = {m}", rows.len());
        let c = cols_of(n, s);
        let mut out = Vec::with_capacity(m * c);
        for row in rows {
            let row = row.as_array().unwrap();
            if row.first().is_some_and(|e| e.is_object()) || row.is_empty() {
                // sparse rows (the catalog's addition-reduced files): [{"index": i, "value": v}, ...]
                let mut dense = vec![0u32; c];
                for e in row {
                    let i = e["index"].as_u64().expect("sparse entry without an index") as usize;
                    assert!(i < c, "sparse index {i} out of range {c}");
                    dense[i] = entry_mod(&e["value"]) as u32;
                }
                out.extend(dense);
            } else {
                assert_eq!(row.len(), c);
                out.extend(row.iter().map(|v| entry_mod(v) as u32));
            }
        }
        x[s] = out;
    }
    Scheme { n, m, x }
}

/// Delete one index of slot `slot` (0 = I rows of A, 1 = J, 2 = K).  Products with a zero factor die; the
/// order of the survivors is kept (the order of kron_project.py's exact output).
fn project(sc: &Scheme, slot: usize, index: usize) -> Scheme {
    let n = sc.n;
    assert!(index < n[slot], "index {index} out of range for slot {slot} of {:?}", n);
    let keep: Vec<Vec<usize>> = (0..3).map(|t| (0..n[t]).filter(|&j| !(t == slot && j == index)).collect()).collect();
    let (ki, kj, kk) = (&keep[0], &keep[1], &keep[2]);
    let cu: Vec<usize> = ki.iter().flat_map(|&i| kj.iter().map(move |&j| i * n[1] + j)).collect();
    let cv: Vec<usize> = kj.iter().flat_map(|&j| kk.iter().map(move |&k| j * n[2] + k)).collect();
    let cw: Vec<usize> = kk.iter().flat_map(|&k| ki.iter().map(move |&i| k * n[0] + i)).collect();
    let cs = [cu, cv, cw];
    let mut n2 = n;
    n2[slot] -= 1;
    let mut x: [Vec<u32>; 3] = [vec![], vec![], vec![]];
    let mut m2 = 0;
    for t in 0..sc.m {
        let rows: Vec<Vec<u32>> = (0..3).map(|s| cs[s].iter().map(|&c| sc.row(s, t)[c]).collect()).collect();
        if rows.iter().all(|r| r.iter().any(|&v| v != 0)) {
            for s in 0..3 {
                x[s].extend_from_slice(&rows[s]);
            }
            m2 += 1;
        }
    }
    Scheme { n: n2, m: m2, x }
}

/// Wrong entries of C = A B over F_p on random A, B (the Brent equations, probabilistically).
/// Layout as in the catalog: u is I x J, v is J x K, w is K x I (index k * n0 + i).
fn brent_check(sc: &Scheme, trials: usize, seed: u64) -> usize {
    let [n0, n1, n2] = sc.n;
    let mut rng = Rng::new(seed);
    let mut bad = 0;
    for _ in 0..trials {
        let a: Vec<u64> = (0..n0 * n1).map(|_| rng.below(P)).collect();
        let b: Vec<u64> = (0..n1 * n2).map(|_| rng.below(P)).collect();
        let mut c = vec![0u64; n2 * n0];
        for t in 0..sc.m {
            let ua = sc.row(0, t).iter().zip(&a).fold(0u64, |s, (&x, &y)| (s + x as u64 * y) % P);
            let vb = sc.row(1, t).iter().zip(&b).fold(0u64, |s, (&x, &y)| (s + x as u64 * y) % P);
            let f = ua * vb % P;
            if f == 0 {
                continue;
            }
            for (ci, &w) in c.iter_mut().zip(sc.row(2, t)) {
                *ci = (*ci + f * w as u64) % P;
            }
        }
        for i in 0..n0 {
            for k in 0..n2 {
                let mut e = 0u64;
                for j in 0..n1 {
                    e = (e + a[i * n1 + j] * b[j * n2 + k]) % P;
                }
                if c[k * n0 + i] != e {
                    bad += 1;
                }
            }
        }
    }
    bad
}

// ---------------------------------------------------------------- Gram matrices and the null space

/// X X^T modulo p (m x m, row-major).
fn gram(x: &[u32], m: usize, c: usize) -> Vec<u64> {
    let mut g = vec![0u64; m * m];
    g.par_chunks_mut(m).enumerate().for_each(|(s, gs)| {
        let rs = &x[s * c..(s + 1) * c];
        for t in 0..m {
            let rt = &x[t * c..(t + 1) * c];
            let mut acc = 0u64; // c <= 2^12 terms below 2^40: no overflow
            for (&a, &b) in rs.iter().zip(rt) {
                acc += a as u64 * b as u64;
            }
            gs[t] = acc % P;
        }
    });
    g
}

/// The Gram matrix of the Kronecker products for direction d: (X_r X_r^T) o (X_c X_c^T).
fn kron_gram(sc: &Scheme, d: usize) -> Vec<u64> {
    let (r, c) = RC[d];
    let (gr, gc) = rayon::join(|| gram(&sc.x[r], sc.m, sc.cols(r)), || gram(&sc.x[c], sc.m, sc.cols(c)));
    gr.into_par_iter().zip(gc.into_par_iter()).map(|(a, b)| a * b % P).collect()
}

/// Null space of a symmetric m x m matrix modulo p.  Returns rows n_i (k of them, length m) with G n_i = 0,
/// n_i[f_i] = 1 and n_i[f_j] = 0 for the other free columns f_j.  Forward elimination with lazy reduction
/// (an entry receives at most m updates below 2^40 each), then back substitution per free column.
fn null_space(g: Vec<u64>, m: usize) -> Vec<Vec<u32>> {
    let mut rows: Vec<Vec<u64>> = g.chunks(m).map(|r| r.to_vec()).collect();
    let mut pc: Vec<usize> = Vec::new(); // pivot column of row i
    let mut r = 0;
    for c in 0..m {
        if r == m {
            break;
        }
        let mut piv = None;
        for i in r..m {
            rows[i][c] %= P;
            if piv.is_none() && rows[i][c] != 0 {
                piv = Some(i);
            }
        }
        let Some(i) = piv else { continue };
        rows.swap(r, i);
        {
            let row = &mut rows[r];
            let f = inv(row[c]);
            for v in row[c..].iter_mut() {
                *v = *v % P * f % P;
            }
        }
        let (top, rest) = rows.split_at_mut(r + 1);
        let pr = &top[r];
        rest.par_iter_mut().with_min_len(8).for_each(|row| {
            let f = row[c]; // reduced above
            if f != 0 {
                let cf = P - f;
                for (v, &q) in row[c + 1..].iter_mut().zip(&pr[c + 1..]) {
                    *v += cf * q;
                }
                row[c] = 0;
            }
        });
        pc.push(c);
        r += 1;
    }
    let mut is_piv = vec![false; m];
    for &c in &pc {
        is_piv[c] = true;
    }
    let free: Vec<usize> = (0..m).filter(|&c| !is_piv[c]).collect();
    let rows = &rows[..r];
    free.par_iter()
        .map(|&f| {
            let mut x = vec![0u64; m];
            x[f] = 1;
            for i in (0..r).rev() {
                let row = &rows[i];
                let c = pc[i];
                let mut acc = 0u64; // terms below 2^40, at most 2^11 of them... reduce every 4096 terms anyway
                let mut cnt = 0;
                for j in c + 1..m {
                    if x[j] != 0 {
                        acc += (row[j] % P) * x[j];
                        cnt += 1;
                        if cnt == 4096 {
                            acc %= P;
                            cnt = 0;
                        }
                    }
                }
                x[c] = (P - acc % P) % P;
            }
            x.into_iter().map(|v| v as u32).collect()
        })
        .collect()
}

// ---------------------------------------------------------------- the pivot search

fn inv_matrix(a: &[Vec<u64>]) -> Option<Vec<Vec<u64>>> {
    let k = a.len();
    let mut m: Vec<Vec<u64>> = (0..k)
        .map(|i| {
            let mut r = a[i].clone();
            r.extend((0..k).map(|j| (i == j) as u64));
            r
        })
        .collect();
    for c in 0..k {
        let i = (c..k).find(|&i| m[i][c] % P != 0)?;
        m.swap(c, i);
        let f = inv(m[c][c]);
        for v in m[c].iter_mut() {
            *v = *v * f % P;
        }
        let pr = m[c].clone();
        for (i, row) in m.iter_mut().enumerate() {
            if i != c && row[c] != 0 {
                let f = P - row[c];
                for (v, &q) in row.iter_mut().zip(&pr) {
                    *v = (*v + f * q) % P;
                }
            }
        }
    }
    Some(m.into_iter().map(|r| r[k..].to_vec()).collect())
}

/// k independent products, those with most companions first (kron_kill.start_pivots).
fn start_pivots(nn: &[Vec<u32>], f: &[u32], c: usize, rng: &mut Rng) -> Vec<usize> {
    let k = nn.len();
    let m = nn[0].len();
    let supp: Vec<usize> = (0..m).filter(|&t| nn.iter().any(|r| r[t] != 0)).collect();
    let rv: Vec<[u64; 2]> = (0..k + c).map(|_| [rng.field(), rng.field()]).collect();
    let mut pt: Vec<Vec<u64>> = Vec::with_capacity(supp.len());
    let mut keys: Vec<u64> = Vec::with_capacity(supp.len());
    for &t in &supp {
        let first = nn.iter().map(|r| r[t]).find(|&v| v != 0).unwrap() as u64;
        let sc = inv(first);
        let col: Vec<u64> = nn.iter().map(|r| r[t] as u64 * sc % P).collect();
        let mut h = [0u64; 2];
        for (j, &v) in col.iter().enumerate() {
            for e in 0..2 {
                h[e] = (h[e] + v * rv[j][e]) % P;
            }
        }
        for (j, &v) in f[t * c..(t + 1) * c].iter().enumerate() {
            let v = v as u64 * sc % P;
            for e in 0..2 {
                h[e] = (h[e] + v * rv[k + j][e]) % P;
            }
        }
        keys.push(h[0] * P + h[1]);
        pt.push(col);
    }
    let mut cnt: HashMap<u64, usize> = HashMap::new();
    for &key in &keys {
        *cnt.entry(key).or_default() += 1;
    }
    let mut order: Vec<(usize, u64, usize)> = (0..supp.len()).map(|i| (usize::MAX - cnt[&keys[i]], rng.next(), i)).collect();
    order.sort_unstable();
    let mut basis: Vec<(usize, Vec<u64>)> = Vec::new();
    let mut jj = Vec::new();
    for &(_, _, i) in &order {
        let mut v = pt[i].clone();
        for (piv, b) in &basis {
            let f = v[*piv];
            if f != 0 {
                for (x, &y) in v.iter_mut().zip(b) {
                    *x = (*x + (P - f) * y) % P;
                }
            }
        }
        let Some(nz) = v.iter().position(|&x| x != 0) else { continue };
        let s = inv(v[nz]);
        for x in v.iter_mut() {
            *x = *x * s % P;
        }
        basis.push((nz, v));
        jj.push(supp[i]);
        if jj.len() == k {
            break;
        }
    }
    assert_eq!(jj.len(), k);
    jj
}

/// Np = N[:, J]^-1 N and Fp = F - Np^T F[J], from scratch.
fn reduce_at(nn: &[Vec<u32>], f: &[u32], c: usize, jj: &[usize]) -> (Vec<Vec<u64>>, Vec<u64>) {
    let k = nn.len();
    let m = nn[0].len();
    let a: Vec<Vec<u64>> = (0..k).map(|i| jj.iter().map(|&t| nn[i][t] as u64).collect()).collect();
    let ai = inv_matrix(&a).expect("the pivots are independent");
    let np: Vec<Vec<u64>> = (0..k)
        .map(|i| {
            (0..m)
                .map(|t| {
                    let mut s = 0u64;
                    for l in 0..k {
                        s += ai[i][l] * nn[l][t] as u64;
                    }
                    s % P
                })
                .collect()
        })
        .collect();
    let mut fp = vec![0u64; m * c];
    fp.par_chunks_mut(c).enumerate().for_each(|(s, row)| {
        let fs = &f[s * c..(s + 1) * c];
        for e in 0..c {
            let mut acc = fs[e] as u64;
            for j in 0..k {
                let w = np[j][s];
                if w != 0 {
                    acc += (P - w) * f[jj[j] * c + e] as u64;
                }
            }
            row[e] = acc % P;
        }
    });
    (np, fp)
}

fn zero_rows(fp: &[u64], c: usize) -> usize {
    fp.chunks(c).filter(|r| r.iter().all(|&v| v == 0)).count()
}

/// The exchange walk (kron_kill.vertex_search).  Returns (gone, pivots, Fp, steps).
fn vertex_search(nn: &[Vec<u32>], f: &[u32], c: usize, rng: &mut Rng, walk: usize) -> (usize, Vec<usize>, Vec<u64>, usize) {
    let k = nn.len();
    let m = nn[0].len();
    let mut jj = start_pivots(nn, f, c, rng);
    let (mut np, mut fp) = reduce_at(nn, f, c, &jj);
    let rv: Vec<[u64; 2]> = (0..c).map(|_| [rng.field(), rng.field()]).collect();
    let mut h: Vec<[u64; 2]> = (0..m)
        .map(|s| {
            let mut x = [0u64; 2];
            for e in 0..c {
                let v = fp[s * c + e];
                if v != 0 {
                    x[0] = (x[0] + v * rv[e][0]) % P;
                    x[1] = (x[1] + v * rv[e][1]) % P;
                }
            }
            x
        })
        .collect();
    let mut zero: Vec<bool> = fp.chunks(c).map(|r| r.iter().all(|&v| v == 0)).collect();
    let mut score = zero.iter().filter(|&&z| z).count();
    let (mut best, mut best_j) = (score, jj.clone());
    let (mut idle, mut steps) = (0usize, 0usize);
    let mut buf: Vec<(u64, usize)> = Vec::with_capacity(m);
    let mut fpt = vec![0u64; c];
    while idle <= walk {
        // the best moves: (gain, j, t), one drawn uniformly among the top gain
        let (mut top, mut ntop, mut pick) = (0usize, 0u64, None::<(usize, usize)>);
        for j in 0..k {
            buf.clear();
            for (s, &w) in np[j].iter().enumerate() {
                if w != 0 {
                    let q = inv(w);
                    buf.push((h[s][0] * q % P * P + h[s][1] * q % P, s));
                }
            }
            buf.sort_unstable();
            let z = if buf.first().map(|x| x.0) == Some(0) { buf.iter().take_while(|x| x.0 == 0).count() } else { 0 };
            let mut i = 0;
            while i < buf.len() {
                let key = buf[i].0;
                let mut e = i;
                while e < buf.len() && buf[e].0 == key {
                    e += 1;
                }
                let cnt = e - i;
                if key != 0 && cnt >= z {
                    let g = cnt - z;
                    if pick.is_none() || g > top {
                        top = g;
                        ntop = 1;
                        pick = Some((j, buf[i].1));
                    } else if g == top {
                        ntop += 1;
                        if rng.below(ntop) == 0 {
                            pick = Some((j, buf[i].1));
                        }
                    }
                }
                i = e;
            }
        }
        let Some((j, t)) = pick else { break };
        let g = top;
        if g == 0 {
            idle += 1;
        }
        // exchange pivot j for product t
        let it = inv(np[j][t]);
        let row: Vec<u64> = np[j].iter().map(|&v| v * it % P).collect();
        let col: Vec<u64> = (0..k).map(|i| np[i][t]).collect();
        for i in 0..k {
            if i != j && col[i] != 0 {
                let cf = P - col[i];
                for (v, &q) in np[i].iter_mut().zip(&row) {
                    if q != 0 {
                        *v = (*v + cf * q) % P;
                    }
                }
            }
        }
        np[j] = row.clone();
        fpt.copy_from_slice(&fp[t * c..(t + 1) * c]);
        let ht = h[t];
        for s in 0..m {
            let q = row[s];
            if q == 0 {
                continue;
            }
            let cf = P - q;
            let fs = &mut fp[s * c..(s + 1) * c];
            let mut all0 = true;
            for (v, &y) in fs.iter_mut().zip(&fpt) {
                if y != 0 {
                    *v = (*v + cf * y) % P;
                }
                all0 &= *v == 0;
            }
            h[s] = [(h[s][0] + cf * ht[0]) % P, (h[s][1] + cf * ht[1]) % P];
            if all0 != zero[s] {
                if all0 {
                    score += 1
                } else {
                    score -= 1
                }
                zero[s] = all0;
            }
        }
        jj[j] = t;
        steps += 1;
        debug_assert_eq!(score, zero_rows(&fp, c));
        if score > best {
            best = score;
            best_j = jj.clone();
            idle = 0;
        }
    }
    let (_, fp) = reduce_at(nn, f, c, &best_j); // from scratch: no drift
    let gone = zero_rows(&fp, c);
    assert_eq!(gone, best, "the walk's count and the recomputed scheme differ");
    (gone, best_j, fp, steps)
}

struct Step {
    d: usize,
    nullity: usize,
    gone: usize,
    pivots: Vec<usize>,
    fp: Vec<u64>,
    steps: usize,
    /// products with a nonzero entry in some dependency (what an exact replay has to look at)
    support: Vec<usize>,
}

fn best_step(sc: &Scheme, d: usize, seed: u64, walk: usize, restarts: usize) -> Option<Step> {
    let g = kron_gram(sc, d);
    let nn = null_space(g, sc.m);
    if nn.is_empty() {
        return None;
    }
    let c = sc.cols(d);
    let f = &sc.x[d];
    let runs: Vec<(usize, Vec<usize>, Vec<u64>, usize)> = (0..restarts)
        .into_par_iter()
        .map(|r| {
            let mut rng = Rng::new(seed ^ (r as u64 + 1).wrapping_mul(0xA24B_AED4_963E_E407));
            vertex_search(&nn, f, c, &mut rng, walk)
        })
        .collect();
    let (gone, pivots, fp, steps) = runs.into_iter().rev().max_by_key(|x| x.0).unwrap(); // ties: the first restart
    let support: Vec<usize> = (0..sc.m).filter(|&t| nn.iter().any(|r| r[t] != 0)).collect();
    Some(Step { d, nullity: nn.len(), gone, pivots, fp, steps, support })
}

/// Reduce until no direction is deficient, at every step in the direction that removes most products.
fn trial(sc: &Scheme, seed: u64, walk: usize, restarts: usize) -> (Scheme, Vec<Value>) {
    let mut sc = sc.clone();
    let mut path = Vec::new();
    let mut rng = Rng::new(seed);
    loop {
        let base = rng.next();
        let cands: Vec<Step> = (0..3usize)
            .into_par_iter()
            .filter_map(|d| best_step(&sc, d, base ^ (d as u64 + 1).wrapping_mul(0xD6E8_FEB8_6659_FD93), walk, restarts))
            .collect();
        if cands.is_empty() {
            return (sc, path);
        }
        let top = cands.iter().map(|s| s.gone).max().unwrap();
        let tied: Vec<&Step> = cands.iter().filter(|s| s.gone == top).collect();
        let b = tied[rng.below(tied.len() as u64) as usize];
        let c = sc.cols(b.d);
        let keep: Vec<usize> = (0..sc.m).filter(|&s| b.fp[s * c..(s + 1) * c].iter().any(|&v| v != 0)).collect();
        let piv: std::collections::HashSet<usize> = b.pivots.iter().copied().collect();
        let dead: Vec<usize> = (0..sc.m).filter(|s| !piv.contains(s) && keep.binary_search(s).is_err()).collect();
        let seen: serde_json::Map<String, Value> =
            cands.iter().map(|s| (s.d.to_string(), json!([s.nullity, s.gone]))).collect();
        path.push(json!({"m": sc.m, "direction": b.d, "nullity": b.nullity, "pivots": b.pivots, "support": b.support, "also_zero": dead,
                         "m_out": keep.len(), "exchange_steps": b.steps, "seen": seen}));
        let mut x: [Vec<u32>; 3] = [vec![], vec![], vec![]];
        for s in 0..3 {
            let cs = sc.cols(s);
            for &t in &keep {
                if s == b.d {
                    x[s].extend(b.fp[t * cs..(t + 1) * cs].iter().map(|&v| v as u32));
                } else {
                    x[s].extend_from_slice(sc.row(s, t));
                }
            }
        }
        sc = Scheme { n: sc.n, m: keep.len(), x };
    }
}

// ---------------------------------------------------------------- driver

fn shape_key(n: [usize; 3]) -> String {
    let mut v = n.to_vec();
    v.sort();
    format!("{}x{}x{}", v[0], v[1], v[2])
}

fn parse_del(s: &str) -> (usize, usize) {
    let slot = "IJK".find(&s[..1]).unwrap_or_else(|| panic!("bad deletion {s}"));
    (slot, s[1..].parse().unwrap_or_else(|_| panic!("bad deletion {s}")))
}

fn sequences(spec: &str, n: [usize; 3]) -> Vec<String> {
    if spec == "." {
        return vec![String::new()];
    }
    if let Some(pre) = spec.strip_prefix("next:") {
        let pre: Vec<&str> = pre.split(',').filter(|x| !x.is_empty()).collect();
        let mut cur = n;
        for d in &pre {
            cur[parse_del(d).0] -= 1;
        }
        let mut out = Vec::new();
        for s in 0..3 {
            for i in 0..cur[s] {
                let mut v: Vec<String> = pre.iter().map(|x| x.to_string()).collect();
                v.push(format!("{}{}", &"IJK"[s..s + 1], i));
                out.push(v.join(","));
            }
        }
        return out;
    }
    if spec == "pairs" {
        let all: Vec<(usize, usize)> = (0..3).flat_map(|s| (0..n[s]).map(move |i| (s, i))).collect();
        let mut out = Vec::new();
        for a in 0..all.len() {
            for b in a + 1..all.len() {
                let ((s1, i1), (s2, i2)) = (all[b], all[a]); // the larger index first: both index the original
                out.push(format!("{}{},{}{}", &"IJK"[s1..s1 + 1], i1, &"IJK"[s2..s2 + 1], i2));
            }
        }
        return out;
    }
    spec.split(';').filter(|s| !s.is_empty()).map(|s| s.to_string()).collect()
}

struct Opts {
    walk: usize,
    restarts: usize,
    seed: u64,
    each: bool,
    brent: usize,
}

fn run_seq(src: &Scheme, name: &str, seq: &str, o: &Opts) -> (Scheme, Vec<Value>, usize) {
    let dels: Vec<&str> = seq.split(',').filter(|x| !x.is_empty()).collect();
    let mut sc = src.clone();
    let mut stages = Vec::new();
    let tag_seed = |tag: &str| hash_str(&format!("{name}|{tag}")) ^ o.seed.wrapping_mul(0x2545_F491_4F6C_DD1D);
    if dels.is_empty() {
        let (y, path) = trial(&sc, tag_seed(""), o.walk, o.restarts);
        stages.push(json!({"delete": "", "n": sc.n, "m_in": sc.m, "alive": sc.m, "steps": path, "m_out": y.m}));
        sc = y;
    }
    for (q, d) in dels.iter().enumerate() {
        let (slot, i) = parse_del(d);
        let m_in = sc.m;
        let y = project(&sc, slot, i);
        let alive = y.m;
        let tag = dels[..=q].join(",");
        let (y, path) = if o.each || q + 1 == dels.len() { trial(&y, tag_seed(&tag), o.walk, o.restarts) } else { (y, vec![]) };
        stages.push(json!({"delete": d, "n": y.n, "m_in": m_in, "alive": alive, "steps": path, "m_out": y.m}));
        sc = y;
        if sc.m == 0 {
            break;
        }
    }
    let bad = if sc.m > 0 { brent_check(&sc, o.brent, hash_str(seq) ^ 0x5EED) } else { usize::MAX };
    (sc, stages, bad)
}

fn describe(stages: &[Value]) -> String {
    stages
        .iter()
        .map(|r| {
            let mut s = format!("{}: {} alive", r["delete"].as_str().unwrap_or(""), r["alive"]);
            for st in r["steps"].as_array().unwrap() {
                let gone = st["m"].as_u64().unwrap() - st["m_out"].as_u64().unwrap();
                s += &format!(", d{}:{}dep:{}gone", st["direction"], st["nullity"], gone);
            }
            s + &format!(" -> {}", r["m_out"])
        })
        .collect::<Vec<_>>()
        .join(" | ")
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let mut opt = |key: &str, default: &str| -> String {
        match args.iter().position(|a| a == key) {
            Some(i) => {
                let v = args[i + 1].clone();
                args.drain(i..i + 2);
                v
            }
            None => default.to_string(),
        }
    };
    let walk: usize = opt("--walk", "100").parse().unwrap();
    let restarts: usize = opt("--restarts", "1").parse().unwrap();
    let threads: usize = opt("--threads", "12").parse().unwrap();
    let seed: u64 = opt("--seed", "0").parse().unwrap();
    let mode = opt("--mode", "each");
    let status = opt("--status", "");
    let bar = opt("--bar", "");
    let out = opt("--out", "");
    let paths = opt("--paths", "");
    let brent: usize = opt("--brent", "3").parse().unwrap();
    let nice: i32 = opt("--nice", "10").parse().unwrap();
    let all_paths = if let Some(i) = args.iter().position(|a| a == "--all-paths") {
        args.remove(i);
        true
    } else {
        false
    };
    if args.len() != 2 {
        eprintln!("usage: kronkill SCHEME.json SEQS [--walk W] [--restarts R] [--threads T] [--seed S] [--mode each|end] [--status STATUS.json] [--bar SHAPE=RANK,...] [--out OUT.csv] [--paths DIR] [--all-paths] [--brent T] [--nice N]");
        std::process::exit(2);
    }
    unsafe {
        libc::nice(nice);
    }
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    let (path, spec) = (&args[0], &args[1]);
    let t0 = Instant::now();
    inv_table();
    let src = load(path);
    let name = std::path::Path::new(path).file_name().unwrap().to_string_lossy().to_string();
    let mut best: HashMap<String, HashMap<String, u64>> = HashMap::new();
    if !status.is_empty() {
        let st: Value = serde_json::from_str(&std::fs::read_to_string(&status).expect("status")).expect("status JSON");
        for (k, v) in st.as_object().unwrap() {
            if let Some(r) = v.get("ranks").and_then(|r| r.as_object()) {
                best.insert(k.clone(), r.iter().filter_map(|(f, x)| x.as_u64().map(|x| (f.clone(), x))).collect());
            }
        }
    }
    for item in bar.split(',').filter(|x| !x.is_empty()) {
        let (k, v) = item.split_once('=').unwrap();
        let v: u64 = v.parse().unwrap();
        let e = best.entry(k.to_string()).or_default().entry("Q".to_string()).or_insert(v);
        *e = (*e).min(v);
    }
    let o = Opts { walk, restarts, seed, each: mode == "each", brent };
    let seqs = sequences(spec, src.n);
    println!("{name}: {:?} with {} products (loaded in {:.1} s); {} deletion sequences ({}), mode {mode}, walk {walk}, restarts {restarts}, {threads} threads, seed {seed}",
             src.n, src.m, t0.elapsed().as_secs_f64(), seqs.len(), &spec[..spec.len().min(60)]);
    if !paths.is_empty() {
        std::fs::create_dir_all(&paths).unwrap();
    }
    let csv = std::sync::Mutex::new(if out.is_empty() {
        None
    } else {
        let mut f = std::fs::File::create(&out).unwrap();
        writeln!(f, "source,sequence,shape,m_out,brent_wrong,stages,best_Q,best_Z,best_ZT,seconds").unwrap();
        Some(f)
    });
    let results = std::sync::Mutex::new(Vec::<(String, usize)>::new());
    let nbelow = std::sync::atomic::AtomicUsize::new(0);
    seqs.par_iter().for_each(|seq| {
        let t1 = Instant::now();
        let (sc, stages, bad) = run_seq(&src, &name, seq, &o);
        let dt = t1.elapsed().as_secs_f64();
        let key = shape_key(sc.n);
        let b = best.get(&key);
        let q = b.and_then(|b| b.get("Q")).copied();
        let desc = describe(&stages);
        let flag = if bad != 0 {
            format!("   BRENT FAILS modulo p ({bad} wrong entries) -- ignore and investigate")
        } else if let Some(q) = q {
            if (sc.m as u64) < q {
                nbelow.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                format!("   <<< BELOW Q {q}")
            } else if sc.m as u64 == q {
                format!("   (ties Q {q})")
            } else {
                String::new()
            }
        } else if b.is_none() && !best.is_empty() {
            "   (shape not in the catalog)".to_string()
        } else {
            String::new()
        };
        let get = |f: &str| b.and_then(|b| b.get(f)).map(|x| x.to_string()).unwrap_or_default();
        println!("{seq}: {key} {desc}; catalog Q {} Z {} ZT {}{flag} ({dt:.1} s)", get("Q"), get("Z"), get("ZT"));
        if let Some(f) = csv.lock().unwrap().as_mut() {
            writeln!(f, "{name},\"{seq}\",{key},{},{bad},\"{desc}\",{},{},{},{dt:.1}", sc.m, get("Q"), get("Z"), get("ZT")).unwrap();
            f.flush().unwrap();
        }
        let below = bad == 0 && q.is_some_and(|q| (sc.m as u64) < q);
        if !paths.is_empty() && (all_paths || below) {
            let pj = json!({"source": path, "sequence": seq, "n": sc.n, "m_out": sc.m, "prime": P, "mode": mode,
                            "walk": walk, "restarts": restarts, "seed": seed, "stages": stages});
            let fname = format!("{paths}/{key}_m{}_{}.path.json", sc.m, if seq.is_empty() { "none".into() } else { seq.replace(',', "_") });
            std::fs::write(fname, serde_json::to_string(&pj).unwrap()).unwrap();
        }
        results.lock().unwrap().push((key, sc.m));
    });
    let res = results.into_inner().unwrap();
    let mut keys: Vec<&String> = res.iter().map(|x| &x.0).collect();
    keys.sort();
    keys.dedup();
    for k in keys {
        let v: Vec<usize> = res.iter().filter(|x| &x.0 == k).map(|x| x.1).collect();
        println!("  {k}: best {}, worst {} over {} sequences; catalog {:?}", v.iter().min().unwrap(), v.iter().max().unwrap(), v.len(), best.get(k));
    }
    println!("done: {} sequences, {} below the catalog's Q rank, {:.0} s", seqs.len(), nbelow.into_inner(), t0.elapsed().as_secs_f64());
}
