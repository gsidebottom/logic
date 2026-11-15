//! kresr: the k-subset re-solve over the rationals and the reals.
//!
//! kres decides over F2 whether k products of a scheme can be rewritten with k - 1.  A rewrite over
//! Q whose constants have odd denominators reduces mod 2, so kres sees it; one that needs halves, or
//! irrational constants, it cannot see.  This tool asks the same question in characteristic 0.
//!
//! Candidates.  The sum R of k products has rank k unless each of its three flattenings has rank
//! below k, and a flattening has rank k unless the k factors of its slot are dependent or the k
//! Kronecker products of the other two slots are.  A dependency over Q among integer vectors
//! with no common factor gives one mod 2, so the subsets kres prints as R candidates (run without
//! --decide) contain every subset that can be reduced over Q or R: they are this tool's input.
//!
//! Stage 1, exact.  The three flattening ranks of R mod p = 2^61 - 1, from the scheme's rational
//! entries: rank(sum_t (a_t (x) b_t) c_t^T) = rank C - dim(col C meet left-null KR_ab), all in
//! F_p^k.  A rank mod p is at most the rank over Q, so a flattening of rank k mod p proves that
//! R has rank exactly k: the subset is irreducible over any field of characteristic 0.
//!
//! Stage 2, numerical.  The survivors: R is compressed to its factor spans (a tensor of at most
//! k x k x k) and a rank-(k - 1) decomposition is sought by Levenberg-Marquardt from warm starts
//! (the k products less one, perturbed) and random ones: a light pass for every subset, the full
//! pass for those it brings within 0.05.  A residual below 1e-9 with bounded
//! factors is a reduction (written out, in the ambient coordinates); otherwise the subset stays
//! open with its best residual: a search, not a proof.
//!
//!   kresr SCHEME.json --all KMIN-KMAX ...      every k-subset, without a candidate list (small schemes)
//!   kresr SCHEME.json LINES [--threads T] [--light N] [--starts N] [--out DIR] [--max-lines N]
//! SCHEME.json: a catalog scheme (n, u, v, w; entries integers or fractions), products in the order
//! of the .bits file kres read; LINES: kres output, the lines "R k=K dims=.. idx=i,j,..".

use rayon::prelude::*;
use serde_json::Value;
use std::io::{BufRead, Write};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

const P: u64 = (1u64 << 61) - 1;
fn mulm(a: u64, b: u64) -> u64 { ((a as u128 * b as u128) % P as u128) as u64 }
fn powm(mut a: u64, mut e: u64) -> u64 { let mut r = 1; while e > 0 { if e & 1 == 1 { r = mulm(r, a); } a = mulm(a, a); e >>= 1; } r }
fn invm(a: u64) -> u64 { powm(a, P - 2) }
fn subm(a: u64, b: u64) -> u64 { if a >= b { a - b } else { a + P - b } }

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn unif(&mut self) -> f64 { ((self.next() >> 11) as f64 + 0.5) / 9007199254740992.0 }
    fn normal(&mut self) -> f64 { (-2.0 * self.unif().ln()).sqrt() * (2.0 * std::f64::consts::PI * self.unif()).cos() }
}

/// a rational entry as (value, value mod p)
fn num(v: &Value) -> (f64, u64) {
    let frac = |a: i64, b: i64| -> (f64, u64) {
        let m = |x: i64| -> u64 { if x >= 0 { x as u64 % P } else { P - ((-x) as u64 % P) } };
        (a as f64 / b as f64, mulm(m(a), invm(m(b))))
    };
    if let Some(x) = v.as_i64() { return frac(x, 1); }
    if let Some(x) = v.as_f64() { assert!(x.fract() == 0.0, "a non-integer number: write it as a fraction string"); return frac(x as i64, 1); }
    let s = v.as_str().expect("a number or a fraction string");
    match s.split_once('/') { Some((a, b)) => frac(a.trim().parse().unwrap(), b.trim().parse().unwrap()), None => frac(s.trim().parse().unwrap(), 1) }
}

/// rows reduced to echelon form in place (mod p); returns the rank.  `aug` columns ride along untouched by pivoting.
fn echelon(rows: &mut [Vec<u64>], ncols: usize) -> usize {
    let mut rk = 0;
    for c in 0..ncols {
        let Some(p) = (rk..rows.len()).find(|&r| rows[r][c] != 0) else { continue };
        rows.swap(rk, p);
        let inv = invm(rows[rk][c]);
        for x in rows[rk].iter_mut() { *x = mulm(*x, inv); }
        let piv = rows[rk].clone();
        for (r, row) in rows.iter_mut().enumerate() {
            if r != rk && row[c] != 0 { let f = row[c]; for (x, y) in row.iter_mut().zip(&piv) { *x = subm(*x, mulm(f, *y)); } }
        }
        rk += 1;
        if rk == rows.len() { break; }
    }
    rk
}

/// the flattening rank mod p of sum_t x_t y_t^T for row sets X (k x p), Y (k x q)
fn flat_rank(x: &[Vec<u64>], y: &[Vec<u64>]) -> usize {
    let k = x.len();
    // the left null space of X: echelon of [X | I]
    let px = x[0].len();
    let mut aug: Vec<Vec<u64>> = (0..k).map(|t| { let mut r = x[t].clone(); r.extend((0..k).map(|s| (s == t) as u64)); r }).collect();
    let rx = echelon(&mut aug, px);
    let null: Vec<Vec<u64>> = aug[rx..].iter().map(|r| r[px..].to_vec()).collect();
    // the column space of Y in F^k: rows of Y^T
    let q = y[0].len();
    let mut cols: Vec<Vec<u64>> = (0..q).map(|c| (0..k).map(|t| y[t][c]).collect()).collect();
    let ry = echelon(&mut cols, k);
    cols.truncate(ry);
    if null.is_empty() { return ry; }
    let mut both = cols;
    both.extend(null.iter().cloned());
    let rsum = echelon(&mut both, k);
    ry - (ry + null.len() - rsum)
}

fn kron_p(a: &[u64], b: &[u64]) -> Vec<u64> { a.iter().flat_map(|&x| b.iter().map(move |&y| if x == 0 || y == 0 { 0 } else { mulm(x, y) })).collect() }

/// orthonormal basis of the row space of the k rows (each of length n) and their coordinates
fn compress(rows: &[&[f64]]) -> (Vec<Vec<f64>>, Vec<Vec<f64>>) {
    let mut basis: Vec<Vec<f64>> = Vec::new();
    for r in rows {
        let mut v = r.to_vec();
        for _ in 0..2 { for b in &basis { let d: f64 = v.iter().zip(b).map(|(x, y)| x * y).sum(); for (x, y) in v.iter_mut().zip(b) { *x -= d * y; } } }
        let nn: f64 = v.iter().map(|x| x * x).sum::<f64>().sqrt();
        if nn > 1e-9 { for x in v.iter_mut() { *x /= nn; } basis.push(v); }
    }
    let coords = rows.iter().map(|r| basis.iter().map(|b| r.iter().zip(b).map(|(x, y)| x * y).sum()).collect()).collect();
    (basis, coords)
}

/// a CP model of rank r for a tensor of shape d: factors u (r x d0), v (r x d1), w (r x d2), row-major
struct Cp { d: [usize; 3], r: usize, x: Vec<f64> }
impl Cp {
    fn off(&self) -> [usize; 3] { [0, self.r * self.d[0], self.r * (self.d[0] + self.d[1])] }
    fn residual(&self, t: &[f64]) -> Vec<f64> {
        let (o, d) = (self.off(), self.d);
        let mut res: Vec<f64> = t.iter().map(|x| -x).collect();
        for p in 0..self.r { for i in 0..d[0] { let a = self.x[o[0] + p * d[0] + i]; if a == 0.0 { continue; }
            for j in 0..d[1] { let ab = a * self.x[o[1] + p * d[1] + j];
                let base = (i * d[1] + j) * d[2];
                for k in 0..d[2] { res[base + k] += ab * self.x[o[2] + p * d[2] + k]; } } } }
        res
    }
    /// gradient of 1/2 |res|^2 and the Gauss-Newton matrix J^T J (n x n, row-major)
    fn grad_normal(&self, res: &[f64]) -> (Vec<f64>, Vec<f64>) {
        let (o, d, r) = (self.off(), self.d, self.r);
        let n = self.x.len();
        let (u, v, w) = (&self.x[..o[1]], &self.x[o[1]..o[2]], &self.x[o[2]..]);
        let mut g = vec![0.0; n];
        for p in 0..r { for i in 0..d[0] { for j in 0..d[1] { let base = (i * d[1] + j) * d[2];
            let (a, b) = (u[p * d[0] + i], v[p * d[1] + j]);
            let mut s = 0.0;
            for k in 0..d[2] { let e = res[base + k]; s += e * w[p * d[2] + k]; g[o[2] + p * d[2] + k] += e * a * b; }
            g[o[0] + p * d[0] + i] += s * b;
            g[o[1] + p * d[1] + j] += s * a;
        } } }
        let gram = |m: &[f64], dd: usize| -> Vec<f64> { let mut q = vec![0.0; r * r]; for p in 0..r { for s in 0..r { q[p * r + s] = (0..dd).map(|i| m[p * dd + i] * m[s * dd + i]).sum(); } } q };
        let (gu, gv, gw) = (gram(u, d[0]), gram(v, d[1]), gram(w, d[2]));
        let mut nm = vec![0.0; n * n];
        for p in 0..r { for s in 0..r {
            let (vw, uw, uv) = (gv[p * r + s] * gw[p * r + s], gu[p * r + s] * gw[p * r + s], gu[p * r + s] * gv[p * r + s]);
            for i in 0..d[0] { nm[(o[0] + p * d[0] + i) * n + o[0] + s * d[0] + i] = vw; }
            for j in 0..d[1] { nm[(o[1] + p * d[1] + j) * n + o[1] + s * d[1] + j] = uw; }
            for k in 0..d[2] { nm[(o[2] + p * d[2] + k) * n + o[2] + s * d[2] + k] = uv; }
            // cross blocks: d res / d u_p[i] . d res / d v_s[j] = u_s[i] v_p[j] (w_p . w_s), and so on
            for i in 0..d[0] { for j in 0..d[1] { let x = u[s * d[0] + i] * v[p * d[1] + j] * gw[p * r + s];
                nm[(o[0] + p * d[0] + i) * n + o[1] + s * d[1] + j] = x; nm[(o[1] + s * d[1] + j) * n + o[0] + p * d[0] + i] = x; } }
            for i in 0..d[0] { for k in 0..d[2] { let x = u[s * d[0] + i] * w[p * d[2] + k] * gv[p * r + s];
                nm[(o[0] + p * d[0] + i) * n + o[2] + s * d[2] + k] = x; nm[(o[2] + s * d[2] + k) * n + o[0] + p * d[0] + i] = x; } }
            for j in 0..d[1] { for k in 0..d[2] { let x = v[s * d[1] + j] * w[p * d[2] + k] * gu[p * r + s];
                nm[(o[1] + p * d[1] + j) * n + o[2] + s * d[2] + k] = x; nm[(o[2] + s * d[2] + k) * n + o[1] + p * d[1] + j] = x; } }
        } }
        (g, nm)
    }
}

/// Cholesky solve of (a + shift I) y = b; None if not positive definite
fn chol_solve(a: &[f64], n: usize, shift: f64, b: &[f64]) -> Option<Vec<f64>> {
    let mut l = a.to_vec();
    for i in 0..n { l[i * n + i] += shift; }
    for j in 0..n {
        let mut d = l[j * n + j];
        for k in 0..j { d -= l[j * n + k] * l[j * n + k]; }
        if d <= 1e-300 { return None; }
        let d = d.sqrt();
        l[j * n + j] = d;
        for i in j + 1..n { let mut s = l[i * n + j]; for k in 0..j { s -= l[i * n + k] * l[j * n + k]; } l[i * n + j] = s / d; }
    }
    let mut y = b.to_vec();
    for i in 0..n { let mut s = y[i]; for k in 0..i { s -= l[i * n + k] * y[k]; } y[i] = s / l[i * n + i]; }
    for i in (0..n).rev() { let mut s = y[i]; for k in i + 1..n { s -= l[k * n + i] * y[k]; } y[i] = s / l[i * n + i]; }
    Some(y)
}

/// Levenberg-Marquardt on 1/2 |res|^2 + mu/2 |x|^2; returns the largest residual entry.  Stops on a plateau: eight
/// steps that lower the cost by less than 0.1% in all while the residual is still large (a local minimum).
fn lm(m: &mut Cp, t: &[f64], iters: usize, mu: f64) -> f64 {
    let n = m.x.len();
    let cost = |m: &Cp| -> (f64, Vec<f64>) { let res = m.residual(t); (0.5 * res.iter().map(|x| x * x).sum::<f64>() + 0.5 * mu * m.x.iter().map(|x| x * x).sum::<f64>(), res) };
    let fmax = |res: &[f64]| res.iter().fold(0.0f64, |a, x| a.max(x.abs()));
    let (mut c, mut res) = cost(m);
    let mut lam = 1e-3;
    let mut mark = (0usize, c);
    for it in 0..iters {
        if fmax(&res) < 1e-13 { break; }
        if it >= mark.0 + 8 { if c > 0.999 * mark.1 && fmax(&res) > 1e-5 { break; } mark = (it, c); }
        let (mut g, nm) = m.grad_normal(&res);
        for i in 0..n { g[i] = -(g[i] + mu * m.x[i]); }
        let mut moved = false;
        for _ in 0..25 {
            if let Some(step) = chol_solve(&nm, n, mu + lam, &g) {
                let old = m.x.clone();
                for i in 0..n { m.x[i] += step[i]; }
                let (c2, r2) = cost(m);
                if c2 < c { c = c2; res = r2; lam = (lam / 3.0).max(1e-15); moved = true; break; }
                m.x = old;
            }
            lam *= 4.0;
        }
        if !moved { break; }
    }
    fmax(&res)
}

struct Scheme { g: [usize; 3], r: usize, f: [Vec<Vec<f64>>; 3], fp: [Vec<Vec<u64>>; 3] }

fn load(path: &str) -> Scheme {
    let d: Value = serde_json::from_str(&std::fs::read_to_string(path).expect("scheme file")).expect("JSON");
    let g: Vec<usize> = d["n"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as usize).collect();
    let mat = |k: &str| -> (Vec<Vec<f64>>, Vec<Vec<u64>>) {
        let rows: Vec<Vec<(f64, u64)>> = d[k].as_array().unwrap().iter().map(|row| row.as_array().unwrap().iter().map(num).collect()).collect();
        (rows.iter().map(|r| r.iter().map(|x| x.0).collect()).collect(), rows.iter().map(|r| r.iter().map(|x| x.1).collect()).collect())
    };
    let ((u, up), (v, vp), (w, wp)) = (mat("u"), mat("v"), mat("w"));
    Scheme { g: [g[0], g[1], g[2]], r: u.len(), f: [u, v, w], fp: [up, vp, wp] }
}

enum Verdict { Proved, Reduced(f64, Vec<[Vec<f64>; 3]>), Open(f64, [usize; 3]) }

fn decide(s: &Scheme, idx: &[usize], light: usize, starts: usize, seed: u64) -> Verdict {
    let k = idx.len();
    // stage 1: flattening ranks mod p
    let fp: [Vec<Vec<u64>>; 3] = [0, 1, 2].map(|q| idx.iter().map(|&t| s.fp[q][t].clone()).collect());
    let rank_of = |rows: &[Vec<u64>]| -> usize { let mut m = rows.to_vec(); let n = m[0].len(); echelon(&mut m, n) };
    let full: [bool; 3] = [0, 1, 2].map(|q| rank_of(&fp[q]) == k);
    let mut ranks = [0usize; 3];
    for q in 0..3 {
        let (a, b) = ((q + 1) % 3, (q + 2) % 3);
        if !full[q] { continue; }
        let kr: Vec<Vec<u64>> = (0..k).map(|t| kron_p(&fp[a][t], &fp[b][t])).collect();
        if rank_of(&kr) == k { return Verdict::Proved; }
    }
    for q in 0..3 {
        let (a, b) = ((q + 1) % 3, (q + 2) % 3);
        let kr: Vec<Vec<u64>> = (0..k).map(|t| kron_p(&fp[a][t], &fp[b][t])).collect();
        ranks[q] = flat_rank(&kr, &fp[q]);
        if ranks[q] == k { return Verdict::Proved; }
    }
    // stage 2: the compressed tensor and a rank k - 1 fit
    let comp: [(Vec<Vec<f64>>, Vec<Vec<f64>>); 3] = [0, 1, 2].map(|q| { let rows: Vec<&[f64]> = idx.iter().map(|&t| s.f[q][t].as_slice()).collect(); compress(&rows) });
    let d = [comp[0].0.len(), comp[1].0.len(), comp[2].0.len()];
    let mut t = vec![0.0; d[0] * d[1] * d[2]];
    for p in 0..k { for i in 0..d[0] { for j in 0..d[1] { for l in 0..d[2] { t[(i * d[1] + j) * d[2] + l] += comp[0].1[p][i] * comp[1].1[p][j] * comp[2].1[p][l]; } } } }
    let r = k - 1;
    let mut rng = Rng(seed);
    let mut best = f64::INFINITY;
    // a light pass (two warm starts, `light` random ones); the full pass (every warm start, `starts` random ones,
    // longer runs) only where the light pass came within 0.05
    for pass in 0..2 {
        let (nwarm, nrand, its) = if pass == 0 { (2.min(k), light, (40, 80)) } else { (k, starts, (80, 300)) };
        if pass == 1 && best > 0.05 { break; }
        for st in 0..nwarm + nrand {
            let mut m = Cp { d, r, x: vec![0.0; r * (d[0] + d[1] + d[2])] };
            let o = m.off();
            if st < nwarm {                               // warm: the products less one, perturbed
                let dropped = if pass == 0 { (rng.next() % k as u64) as usize } else { st };
                let keep: Vec<usize> = (0..k).filter(|&p| p != dropped).collect();
                for (row, &p) in keep.iter().enumerate() { for q in 0..3 { for i in 0..d[q] { m.x[o[q] + row * d[q] + i] = comp[q].1[p][i] + 0.3 * rng.normal(); } } }
            } else {
                for x in m.x.iter_mut() { *x = rng.normal() * 0.7; }
            }
            lm(&mut m, &t, its.0, 1e-3);
            let f = lm(&mut m, &t, its.1, 0.0);
            let big = m.x.iter().fold(0.0f64, |a, x| a.max(x.abs()));
            if f < 1e-9 && big < 1e3 {
                // back to the ambient coordinates
                let prods = (0..r).map(|p| [0, 1, 2].map(|q| { let n = comp[q].0[0].len(); let mut v = vec![0.0; n]; for (i, b) in comp[q].0.iter().enumerate() { let c = m.x[o[q] + p * d[q] + i]; for (x, y) in v.iter_mut().zip(b) { *x += c * y; } } v })).collect();
                return Verdict::Reduced(f, prods);
            }
            if big < 1e3 { best = best.min(f); }
        }
    }
    Verdict::Open(best, ranks)
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.len() < 2 { eprintln!("usage: kresr SCHEME.json LINES [--threads T] [--light N] [--starts N] [--out DIR] [--max-lines N]"); std::process::exit(2); }
    let opt = |k: &str, d: usize| -> usize { a.iter().position(|x| x == k).map(|i| a[i + 1].parse().unwrap()).unwrap_or(d) };
    let (threads, light, starts, max_lines) = (opt("--threads", 10), opt("--light", 3), opt("--starts", 30), opt("--max-lines", usize::MAX));
    let out = a.iter().position(|x| x == "--out").map(|i| a[i + 1].clone());
    rayon::ThreadPoolBuilder::new().num_threads(threads).build_global().unwrap();
    let s = load(&a[0]);
    println!("# kresr: <{}x{}x{}:{}> from {}; candidates from {}; 2 warm + {light} random starts, and k warm + {starts} random where those come within 0.05", s.g[0], s.g[1], s.g[2], s.r, a[0], a[1]);
    let t0 = std::time::Instant::now();
    let stats: Mutex<std::collections::BTreeMap<usize, [f64; 6]>> = Mutex::new(Default::default());   // per k: lines, proved, reduced, open, best open residual, -
    let found = AtomicU64::new(0);
    let hist: Mutex<std::collections::BTreeMap<(usize, [usize; 3]), usize>> = Mutex::new(Default::default());
    let mut chunk: Vec<Vec<usize>> = Vec::new();
    let mut total = 0usize;
    let run = |chunk: &mut Vec<Vec<usize>>| {
        chunk.par_iter().for_each(|idx| {
            let k = idx.len();
            let v = decide(&s, idx, light, starts, 0x9e37 + idx.iter().fold(0u64, |h, &i| h.wrapping_mul(1000003).wrapping_add(i as u64)));
            let mut st = stats.lock().unwrap();
            let e = st.entry(k).or_insert([0.0, 0.0, 0.0, 0.0, f64::INFINITY, 0.0]);
            e[0] += 1.0;
            match v {
                Verdict::Proved => e[1] += 1.0,
                Verdict::Open(f, ranks) => { e[3] += 1.0; *hist.lock().unwrap().entry((k, ranks)).or_insert(0usize) += 1; if f < e[4] { e[4] = f; println!("open k={k} flattening ranks {ranks:?} best |F| {f:.2e} idx={}", idx.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")); } }
                Verdict::Reduced(f, prods) => {
                    e[2] += 1.0;
                    let nfound = found.fetch_add(1, Ordering::Relaxed);
                    let id = idx.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
                    if nfound < 50 { println!("RED k={k} |F| {f:.1e} idx={id}"); }
                    if let (Some(dir), true) = (&out, nfound < 200) {
                        std::fs::create_dir_all(dir).ok();
                        let j = serde_json::json!({"k": k, "idx": idx, "residual": f, "products": prods.iter().map(|p| serde_json::json!({"a": p[0], "b": p[1], "c": p[2]})).collect::<Vec<_>>()});
                        std::fs::File::create(format!("{dir}/red_k{k}_{nfound}.json")).and_then(|mut fh| fh.write_all(j.to_string().as_bytes())).ok();
                    }
                }
            }
        });
        chunk.clear();
    };
    if let Some(i) = a.iter().position(|x| x == "--all") {
        let (lo, hi) = a[i + 1].split_once('-').map(|(x, y)| (x.parse::<usize>().unwrap(), y.parse::<usize>().unwrap())).expect("--all KMIN-KMAX");
        for k in lo..=hi {
            // subsets by their two smallest members, in parallel
            let pairs: Vec<(usize, usize)> = (0..s.r).flat_map(|i| (i + 1..s.r).map(move |j| (i, j))).collect();
            pairs.par_iter().for_each(|&(i, j)| {
                let mut idx = vec![i, j];
                let mut local: Vec<Vec<usize>> = Vec::new();
                fn rec(idx: &mut Vec<usize>, k: usize, r: usize, out: &mut Vec<Vec<usize>>) {
                    if idx.len() == k { out.push(idx.clone()); return; }
                    for t in idx[idx.len() - 1] + 1..r { idx.push(t); rec(idx, k, r, out); idx.pop(); }
                }
                rec(&mut idx, k, s.r, &mut local);
                let mut tally = [0.0f64; 4];
                let mut bestf = f64::INFINITY;
                for idx in &local {
                    let v = decide(&s, idx, light, starts, 0x9e37 + idx.iter().fold(0u64, |h, &i| h.wrapping_mul(1000003).wrapping_add(i as u64)));
                    tally[0] += 1.0;
                    let id = || idx.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",");
                    match v {
                        Verdict::Proved => tally[1] += 1.0,
                        Verdict::Open(f, ranks) => { tally[3] += 1.0; bestf = bestf.min(f); *hist.lock().unwrap().entry((k, ranks)).or_insert(0usize) += 1;
                            if f < 1e-3 { println!("open k={k} flattening ranks {ranks:?} best |F| {f:.2e} idx={}", id()); } }
                        Verdict::Reduced(f, prods) => { tally[2] += 1.0;
                            let nfound = found.fetch_add(1, Ordering::Relaxed);
                            if nfound < 50 { println!("RED k={k} |F| {f:.1e} idx={}", id()); }
                            if let (Some(dir), true) = (&out, nfound < 200) {
                                std::fs::create_dir_all(dir).ok();
                                let j = serde_json::json!({"k": k, "idx": idx, "residual": f, "products": prods.iter().map(|p| serde_json::json!({"a": p[0], "b": p[1], "c": p[2]})).collect::<Vec<_>>()});
                                std::fs::File::create(format!("{dir}/red_k{k}_{nfound}.json")).and_then(|mut fh| fh.write_all(j.to_string().as_bytes())).ok();
                            } }
                    }
                }
                let mut st = stats.lock().unwrap();
                let e = st.entry(k).or_insert([0.0, 0.0, 0.0, 0.0, f64::INFINITY, 0.0]);
                for q in 0..4 { e[q] += tally[q]; }
                e[4] = e[4].min(bestf);
            });
            let st = stats.lock().unwrap();
            let e = st[&k];
            println!("# k={k}: {} subsets; {} proved irreducible (independent factors and Kronecker products in a slot); {} REDUCED; {} open (best |F| {:.2e}); {:.0} s", e[0], e[1], e[2], e[3], e[4], t0.elapsed().as_secs_f64());
        }
        for ((k, ranks), c) in hist.lock().unwrap().iter() { println!("#   open k={k} flattening ranks {ranks:?}: {c}"); }
        println!("# done, {:.0} s", t0.elapsed().as_secs_f64());
        return;
    }
    let file = std::io::BufReader::new(std::fs::File::open(&a[1]).expect("lines file"));
    for ln in file.lines() {
        let ln = ln.unwrap();
        if !ln.starts_with("R ") { continue; }
        let Some(p) = ln.find("idx=") else { continue };
        chunk.push(ln[p + 4..].split(|c: char| !c.is_ascii_digit()).filter(|x| !x.is_empty()).map(|x| x.parse().unwrap()).collect());
        total += 1;
        if chunk.len() >= 200_000 { run(&mut chunk); eprintln!("# {total} lines, {:.0} s", t0.elapsed().as_secs_f64()); }
        if total >= max_lines { break; }
    }
    run(&mut chunk);
    for (k, e) in stats.lock().unwrap().iter() {
        println!("# k={k}: {} candidates; {} proved irreducible (a flattening of rank k); {} REDUCED; {} open (best |F| {:.2e})", e[0], e[1], e[2], e[3], e[4]);
    }
    for ((k, ranks), c) in hist.lock().unwrap().iter() { println!("#   open k={k} flattening ranks {ranks:?}: {c}"); }
    println!("# done, {:.0} s", t0.elapsed().as_secs_f64());
}
