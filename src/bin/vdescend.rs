//! vdescend: rank descent on the variety of exact matrix-multiplication decompositions.
//!
//! The decompositions of <g1 x g2 x g3> with r products are the zeros of
//! F(U, V, W) = sum_t U_t (x) V_t (x) W_t - T, a real variety V_r.  Its tangent space at a scheme
//! (the kernel of the Jacobian J of F) holds the directions every scheme has -- two rescalings
//! per product and the orbit of GL_g1 x GL_g2 x GL_g3 -- and, where it is larger, MODULI:
//! continuous families of inequivalent schemes.  A flip graph walks such families at the
//! discrete points a small ring allows; here the walk is continuous, and it has a compass.
//! Two products merge into one when they are parallel in two of their three factors.  With
//! p^X_st = 1 - cos^2(angle of X_s, X_t) for a slot X,
//!
//!     D_st = p^U p^V + p^U p^W + p^V p^W,      Phi = sum_{s<t} omega_st log(D_st + delta),
//!
//! Phi falls without bound where a pair becomes mergeable.  A step moves along -grad Phi
//! projected on the moduli (kernel of J with the trivial directions removed: the orbit changes
//! no scheme but every angle), returns to V_r by Levenberg-Marquardt, and is kept if Phi fell;
//! at a critical point or a stall it is a random move along the moduli instead.  Mergeable pairs
//! are merged and the scheme polished to |F| = 0 at the smaller rank, or the merge is refused.
//! No product may grow past a bound: a pair that turns parallel while its norms diverge is a
//! degeneration (border rank), not a reduction.
//!
//! Linear algebra: the normal matrix N = J^T J is assembled from the Gram matrices of the
//! factors without forming J; the projector on the kernel is eps (N + eps)^-1 applied twice
//! (one Cholesky, Accelerate's dpotrf) instead of an eigendecomposition; the trivial directions
//! are orthonormalized once per step.  Runs are independent and run in parallel.
//!
//!   vdescend SCHEME [--runs R] [--steps N] [--seed S] [--threads T] [--kick 0.3] [--bound 30]
//!            [--out DIR] [--moduli] [--quiet]
//!   vdescend trivial:g1xg2xg3 --search RANK [--runs R] [--iters 2000] [--init 0.5] [--mu 1e-2] [--window 25]
//!            random starts at RANK by regularized Levenberg-Marquardt (lm_search)
//!            --sparse [--clamp 0.05]: clamp each scheme found to a sparse one and read it as rational (sparsify)
//!   vdescend SCHEME --warm D [--noise 0.1] ...    the scheme less D products, plus noise, as starts
//!   vdescend trivial:g1xg2xg3 --sym AUT.json [--order 3 | --elem I] --orbits M --fixed F ...
//!            the search among schemes invariant under a group element (matmul/r346/sym/autgroup.py
//!            writes AUT.json): rank q M + F, a q-th of the unknowns
//! SCHEME: a JSON file with n = [g1, g2, g3] and u, v, w (Perminov's catalog format; either
//! orientation of C), or trivial:g1xg2xg3.  --moduli prints the dimension of the tangent space
//! against the trivial directions and exits.

use rayon::prelude::*;
use serde_json::Value;
use std::time::Instant;

#[link(name = "Accelerate", kind = "framework")]
unsafe extern "C" {
    fn dpotrf_(uplo: *const u8, n: *const i32, a: *mut f64, lda: *const i32, info: *mut i32);
    fn dpotrs_(uplo: *const u8, n: *const i32, nrhs: *const i32, a: *const f64, lda: *const i32, b: *mut f64, ldb: *const i32, info: *mut i32);
}

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

#[derive(Clone)]
struct Sch { g: [usize; 3], r: usize, u: Vec<f64>, v: Vec<f64>, w: Vec<f64> }

impl Sch {
    fn dims(&self) -> (usize, usize, usize) { (self.g[0] * self.g[1], self.g[1] * self.g[2], self.g[0] * self.g[2]) }
    fn n(&self) -> usize { let (i, j, k) = self.dims(); self.r * (i + j + k) }
    fn x(&self) -> Vec<f64> { let mut x = self.u.clone(); x.extend_from_slice(&self.v); x.extend_from_slice(&self.w); x }
    fn with_x(&self, x: &[f64]) -> Sch {
        let (i, j, _) = self.dims(); let r = self.r;
        Sch { g: self.g, r, u: x[..r * i].to_vec(), v: x[r * i..r * (i + j)].to_vec(), w: x[r * (i + j)..].to_vec() }
    }
    /// |U_t|^2 + |V_t|^2 + |W_t|^2 per product
    fn norms2(&self) -> Vec<f64> {
        let (i, j, k) = self.dims();
        (0..self.r).map(|t| sq(&self.u[t * i..(t + 1) * i]) + sq(&self.v[t * j..(t + 1) * j]) + sq(&self.w[t * k..(t + 1) * k])).collect()
    }
    /// each product rescaled so that its three factors have equal norms (the same scheme)
    fn balance(&mut self) {
        let (i, j, k) = self.dims();
        for t in 0..self.r {
            let (a, b, c) = (sq(&self.u[t * i..(t + 1) * i]).sqrt(), sq(&self.v[t * j..(t + 1) * j]).sqrt(), sq(&self.w[t * k..(t + 1) * k]).sqrt());
            if a == 0.0 || b == 0.0 || c == 0.0 { continue; }
            let m = (a * b * c).cbrt();
            for x in &mut self.u[t * i..(t + 1) * i] { *x *= m / a; }
            for x in &mut self.v[t * j..(t + 1) * j] { *x *= m / b; }
            for x in &mut self.w[t * k..(t + 1) * k] { *x *= m / c; }
        }
    }
}

fn sq(x: &[f64]) -> f64 { x.iter().map(|a| a * a).sum() }
fn dot(x: &[f64], y: &[f64]) -> f64 { x.iter().zip(y).map(|(a, b)| a * b).sum() }

/// T[(i,j), (j,k), (i,k)] = 1, index (a J + b) K + c
fn tensor(g: [usize; 3]) -> Vec<f64> {
    let (ni, nj, nk) = (g[0] * g[1], g[1] * g[2], g[0] * g[2]);
    let mut t = vec![0.0; ni * nj * nk];
    for i in 0..g[0] { for j in 0..g[1] { for k in 0..g[2] {
        t[((i * g[1] + j) * nj + j * g[2] + k) * nk + i * g[2] + k] = 1.0;
    } } }
    t
}

fn residual(s: &Sch, t: &[f64]) -> Vec<f64> {
    let (ni, nj, nk) = s.dims();
    let mut r: Vec<f64> = t.iter().map(|x| -x).collect();
    for p in 0..s.r {
        let (u, v, w) = (&s.u[p * ni..(p + 1) * ni], &s.v[p * nj..(p + 1) * nj], &s.w[p * nk..(p + 1) * nk]);
        for a in 0..ni {
            if u[a] == 0.0 { continue; }
            for b in 0..nj {
                let ab = u[a] * v[b];
                if ab == 0.0 { continue; }
                let row = &mut r[(a * nj + b) * nk..(a * nj + b + 1) * nk];
                for c in 0..nk { row[c] += ab * w[c]; }
            }
        }
    }
    r
}

/// J^T R: the gradient of 1/2 |F|^2
fn grad_f(s: &Sch, res: &[f64]) -> Vec<f64> {
    let (ni, nj, nk) = s.dims(); let r = s.r;
    let mut g = vec![0.0; s.n()];
    let mut m = vec![0.0; ni * nj];
    for p in 0..r {
        let (u, v, w) = (&s.u[p * ni..(p + 1) * ni], &s.v[p * nj..(p + 1) * nj], &s.w[p * nk..(p + 1) * nk]);
        for ab in 0..ni * nj { m[ab] = dot(&res[ab * nk..(ab + 1) * nk], w); }
        for a in 0..ni { g[p * ni + a] = dot(&m[a * nj..(a + 1) * nj], v); }
        for b in 0..nj { let mut x = 0.0; for a in 0..ni { x += m[a * nj + b] * u[a]; } g[r * ni + p * nj + b] = x; }
        let gw = &mut g[r * (ni + nj) + p * nk..r * (ni + nj) + (p + 1) * nk];
        for a in 0..ni { if u[a] == 0.0 { continue; } for b in 0..nj {
            let ab = u[a] * v[b];
            if ab == 0.0 { continue; }
            let row = &res[(a * nj + b) * nk..(a * nj + b + 1) * nk];
            for c in 0..nk { gw[c] += ab * row[c]; }
        } }
    }
    g
}

fn gram(x: &[f64], r: usize, d: usize) -> Vec<f64> {
    let mut g = vec![0.0; r * r];
    for s in 0..r { for t in s..r { let v = dot(&x[s * d..(s + 1) * d], &x[t * d..(t + 1) * d]); g[s * r + t] = v; g[t * r + s] = v; } }
    g
}

/// N = J^T J for x = (U, V, W), from the Gram matrices
fn normal(s: &Sch) -> Vec<f64> {
    let (ni, nj, nk) = s.dims(); let r = s.r; let n = s.n();
    let (gu, gv, gw) = (gram(&s.u, r, ni), gram(&s.v, r, nj), gram(&s.w, r, nk));
    let (ou, ov, ow) = (0, r * ni, r * (ni + nj));
    let mut m = vec![0.0; n * n];
    for t in 0..r { for q in 0..r {
        let (vw, uw, uv) = (gv[t * r + q] * gw[t * r + q], gu[t * r + q] * gw[t * r + q], gu[t * r + q] * gv[t * r + q]);
        for a in 0..ni { m[(ou + t * ni + a) * n + ou + q * ni + a] = vw; }
        for b in 0..nj { m[(ov + t * nj + b) * n + ov + q * nj + b] = uw; }
        for c in 0..nk { m[(ow + t * nk + c) * n + ow + q * nk + c] = uv; }
        let (ut, vt, wt) = (&s.u[t * ni..(t + 1) * ni], &s.v[t * nj..(t + 1) * nj], &s.w[t * nk..(t + 1) * nk]);
        let (uq, vq) = (&s.u[q * ni..(q + 1) * ni], &s.v[q * nj..(q + 1) * nj]);
        let (gwtq, gvtq, gutq) = (gw[t * r + q], gv[t * r + q], gu[t * r + q]);
        for a in 0..ni {
            let row = (ou + t * ni + a) * n;
            let (x, y) = (gwtq * uq[a], gvtq * uq[a]);
            for b in 0..nj { let val = x * vt[b]; m[row + ov + q * nj + b] = val; m[(ov + q * nj + b) * n + ou + t * ni + a] = val; }
            for c in 0..nk { let val = y * wt[c]; m[row + ow + q * nk + c] = val; m[(ow + q * nk + c) * n + ou + t * ni + a] = val; }
        }
        for b in 0..nj {
            let row = (ov + t * nj + b) * n;
            let x = gutq * vq[b];
            for c in 0..nk { let val = x * wt[c]; m[row + ow + q * nk + c] = val; m[(ow + q * nk + c) * n + ov + t * nj + b] = val; }
        }
        let _ = ut;
    } }
    m
}

/// Cholesky factor of a + shift I (lower, in place); false if not positive definite
fn factor(a: &mut [f64], n: usize, shift: f64) -> bool {
    for i in 0..n { a[i * n + i] += shift; }
    let (ni, mut info) = (n as i32, 0i32);
    unsafe { dpotrf_(b"L".as_ptr(), &ni, a.as_mut_ptr(), &ni, &mut info); }
    info == 0
}
fn solve(fac: &[f64], n: usize, b: &mut [f64]) {
    let (ni, nrhs, mut info) = (n as i32, (b.len() / n) as i32, 0i32);
    unsafe { dpotrs_(b"L".as_ptr(), &ni, &nrhs, fac.as_ptr(), &ni, b.as_mut_ptr(), &ni, &mut info); }
}

/// Levenberg-Marquardt back to the variety; returns max |F|
fn polish(s: &mut Sch, t: &[f64], iters: usize, tol: f64) -> f64 {
    let n = s.n();
    let mut lam = 1e-6;
    let mut res = residual(s, t);
    let mut f2 = sq(&res);
    for _ in 0..iters {
        if res.iter().fold(0.0f64, |m, x| m.max(x.abs())) < tol { break; }
        let nm = normal(s);
        let g = grad_f(s, &res);
        let x = s.x();
        let mut moved = false;
        for _ in 0..12 {
            let mut a = nm.clone();
            let scale = (0..n).map(|i| nm[i * n + i]).fold(0.0f64, f64::max);
            if !factor(&mut a, n, lam * scale.max(1e-300)) { lam *= 10.0; continue; }
            let mut d: Vec<f64> = g.iter().map(|v| -v).collect();
            solve(&a, n, &mut d);
            let x2: Vec<f64> = x.iter().zip(&d).map(|(a, b)| a + b).collect();
            let s2 = s.with_x(&x2);
            let r2 = residual(&s2, t);
            let f22 = sq(&r2);
            if f22 < f2 && f22.is_finite() { *s = s2; res = r2; f2 = f22; lam = (lam / 3.0).max(1e-13); moved = true; break; }
            lam *= 4.0;
        }
        if !moved { break; }
    }
    res.iter().fold(0.0f64, |m, x| m.max(x.abs()))
}

/// the tangent directions every scheme has, orthonormalized: per product two rescalings, and the Lie
/// algebra of GL_g1 x GL_g2 x GL_g3 (A -> X A Y^-1, B -> Y B Z^-1, C -> X^-T C Z^T)
fn trivial_basis(s: &Sch) -> Vec<Vec<f64>> {
    let (ni, nj, nk) = s.dims(); let r = s.r; let n = s.n(); let g = s.g;
    let (ou, ov, ow) = (0, r * ni, r * (ni + nj));
    let mut raw: Vec<Vec<f64>> = Vec::new();
    for t in 0..r {
        let mut a = vec![0.0; n]; let mut b = vec![0.0; n];
        for i in 0..ni { a[ou + t * ni + i] = s.u[t * ni + i]; }
        for j in 0..nj { b[ov + t * nj + j] = s.v[t * nj + j]; }
        for k in 0..nk { a[ow + t * nk + k] = -s.w[t * nk + k]; b[ow + t * nk + k] = -s.w[t * nk + k]; }
        raw.push(a); raw.push(b);
    }
    // A[t][i][j] = u[t*ni + i*g1' ...]: A is g0 x g1, B is g1 x g2, C is g0 x g2
    for p in 0..g[0] { for q in 0..g[0] {       // X = E_pq: dA = E A (row p gets row q), dC = -E^T C (row q gets -row p)
        let mut d = vec![0.0; n];
        for t in 0..r {
            for j in 0..g[1] { d[ou + t * ni + p * g[1] + j] += s.u[t * ni + q * g[1] + j]; }
            for k in 0..g[2] { d[ow + t * nk + q * g[2] + k] -= s.w[t * nk + p * g[2] + k]; }
        }
        raw.push(d);
    } }
    for p in 0..g[1] { for q in 0..g[1] {       // Y = E_pq: dA = -A E (column q gets -column p), dB = E B (row p gets row q)
        let mut d = vec![0.0; n];
        for t in 0..r {
            for i in 0..g[0] { d[ou + t * ni + i * g[1] + q] -= s.u[t * ni + i * g[1] + p]; }
            for k in 0..g[2] { d[ov + t * nj + p * g[2] + k] += s.v[t * nj + q * g[2] + k]; }
        }
        raw.push(d);
    } }
    for p in 0..g[2] { for q in 0..g[2] {       // Z = E_pq: dB = -B E (column q gets -column p), dC = C E^T (column p gets column q)
        let mut d = vec![0.0; n];
        for t in 0..r {
            for j in 0..g[1] { d[ov + t * nj + j * g[2] + q] -= s.v[t * nj + j * g[2] + p]; }
            for i in 0..g[0] { d[ow + t * nk + i * g[2] + p] += s.w[t * nk + i * g[2] + q]; }
        }
        raw.push(d);
    } }
    orthonormalize(raw, 1e-8)
}

/// modified Gram-Schmidt, twice; vectors whose remainder is below tol of their norm are dropped
fn orthonormalize(raw: Vec<Vec<f64>>, tol: f64) -> Vec<Vec<f64>> {
    let mut q: Vec<Vec<f64>> = Vec::new();
    for mut v in raw {
        let n0 = sq(&v).sqrt();
        if n0 == 0.0 { continue; }
        for _ in 0..2 { for b in &q { let c = dot(&v, b); for (x, y) in v.iter_mut().zip(b) { *x -= c * y; } } }
        let n1 = sq(&v).sqrt();
        if n1 > tol * n0 { for x in v.iter_mut() { *x /= n1; } q.push(v); }
    }
    q
}

/// the projector on the moduli at a scheme: kernel of J (eps (N + eps)^-1, twice) minus the trivial directions
struct Proj { fac: Vec<f64>, eps: f64, n: usize, triv: Vec<Vec<f64>> }
impl Proj {
    fn new(s: &Sch) -> Option<Proj> {
        let n = s.n();
        let mut a = normal(s);
        let scale = (0..n).map(|i| a[i * n + i]).fold(0.0f64, f64::max);
        let eps = 1e-9 * scale;
        if !factor(&mut a, n, eps) { return None; }
        Some(Proj { fac: a, eps, n, triv: trivial_basis(s) })
    }
    fn kernel(&self, v: &[f64]) -> Vec<f64> {
        let mut d = v.to_vec();
        for _ in 0..2 { solve(&self.fac, self.n, &mut d); for x in d.iter_mut() { *x *= self.eps; } }
        d
    }
    fn moduli(&self, v: &[f64]) -> Vec<f64> {
        let mut d = self.kernel(v);
        for _ in 0..2 { for b in &self.triv { let c = dot(&d, b); for (x, y) in d.iter_mut().zip(b) { *x -= c * y; } } }
        d
    }
    /// (dimension of the tangent space, of the trivial directions): random probes through the projector
    fn dimensions(&self, rng: &mut Rng, probes: usize) -> (usize, usize) {
        let mut ker = Vec::new();
        for _ in 0..probes { let v: Vec<f64> = (0..self.n).map(|_| rng.normal()).collect(); ker.push(self.kernel(&v)); }
        (orthonormalize(ker, 1e-6).len(), self.triv.len())
    }
}

/// Phi, D (r x r) and optionally the gradient of Phi
fn potential(s: &Sch, om: &[f64], delta: f64, want_grad: bool) -> (f64, Vec<f64>, Vec<f64>) {
    let (ni, nj, nk) = s.dims(); let r = s.r;
    let xs: [(&[f64], usize); 3] = [(&s.u, ni), (&s.v, nj), (&s.w, nk)];
    let gr: Vec<Vec<f64>> = xs.iter().map(|(x, d)| gram(x, r, *d)).collect();
    let p: Vec<Vec<f64>> = gr.iter().map(|g| (0..r * r).map(|i| { let (a, b) = (i / r, i % r); 1.0 - g[i] * g[i] / (g[a * r + a] * g[b * r + b]).max(1e-300) }).collect()).collect();
    let d: Vec<f64> = (0..r * r).map(|i| p[0][i] * p[1][i] + p[0][i] * p[2][i] + p[1][i] * p[2][i]).collect();
    let mut phi = 0.0;
    for a in 0..r { for b in a + 1..r { phi += om[a * r + b] * (d[a * r + b] + delta).ln(); } }
    let mut grad = Vec::new();
    if want_grad {
        grad = vec![0.0; s.n()];
        let offs = [0, r * ni, r * (ni + nj)];
        for q in 0..3 {
            let (x, dim) = xs[q];
            let (o1, o2) = match q { 0 => (1, 2), 1 => (0, 2), _ => (0, 1) };
            let g = &gr[q];
            for a in 0..r {
                let na = g[a * r + a].max(1e-300);
                let mut diag = 0.0;
                let out = offs[q] + a * dim;
                for b in 0..r {
                    if a == b { continue; }
                    let nb = g[b * r + b].max(1e-300);
                    let w = om[a * r + b] * (p[o1][a * r + b] + p[o2][a * r + b]) / (d[a * r + b] + delta);
                    let c = g[a * r + b] * g[a * r + b] / (na * nb);
                    diag += 2.0 * w * c / na;
                    let m = -2.0 * w * g[a * r + b] / (na * nb);
                    for i in 0..dim { grad[out + i] += m * x[b * dim + i]; }
                }
                for i in 0..dim { grad[out + i] += diag * x[a * dim + i]; }
            }
        }
    }
    (phi, d, grad)
}

/// merge the most mergeable pair if D < thresh and the merged scheme polishes to |F| = 0
fn merge(s: &Sch, d: &[f64], t: &[f64], thresh: f64) -> Option<Sch> {
    let (ni, nj, nk) = s.dims(); let r = s.r;
    let (mut best, mut pa, mut pb) = (f64::MAX, 0, 0);
    for a in 0..r { for b in a + 1..r { if d[a * r + b] < best { best = d[a * r + b]; pa = a; pb = b; } } }
    if best > thresh { return None; }
    let xs: [(&[f64], usize); 3] = [(&s.u, ni), (&s.v, nj), (&s.w, nk)];
    let par: Vec<f64> = xs.iter().map(|(x, dm)| {
        let (a, b) = (&x[pa * dm..(pa + 1) * dm], &x[pb * dm..(pb + 1) * dm]);
        dot(a, b).abs() / (sq(a).sqrt() * sq(b).sqrt() + 1e-300)
    }).collect();
    let free = (0..3).min_by(|&a, &b| par[a].partial_cmp(&par[b]).unwrap()).unwrap();   // the slot that carries the sum
    let mut scale = 1.0;
    for q in 0..3 { if q != free { let (x, dm) = xs[q]; let (a, b) = (&x[pa * dm..(pa + 1) * dm], &x[pb * dm..(pb + 1) * dm]); scale *= dot(a, b) / sq(a); } }
    let mut parts: Vec<Vec<f64>> = xs.iter().map(|(x, _)| x.to_vec()).collect();
    { let dm = xs[free].1; for i in 0..dm { let add = scale * parts[free][pb * dm + i]; parts[free][pa * dm + i] += add; } }
    for q in 0..3 { let dm = xs[q].1; parts[q].drain(pb * dm..(pb + 1) * dm); }
    let mut m = Sch { g: s.g, r: r - 1, u: parts[0].clone(), v: parts[1].clone(), w: parts[2].clone() };
    m.balance();
    if polish(&mut m, t, 200, 1e-13) < 1e-10 { m.balance(); Some(m) } else { None }
}

fn weights(r: usize, rng: &mut Rng) -> Vec<f64> {
    let mut om = vec![0.0; r * r];
    for a in 0..r { for b in a + 1..r { let v = rng.normal().exp(); om[a * r + b] = v; om[b * r + a] = v; } }
    om
}

struct Opts { steps: usize, kick: f64, bound: f64, quiet: bool }

/// one run of the descent; returns the scheme reached and max |F|
fn run(start: &Sch, t: &[f64], seed: u64, o: &Opts, tag: &str) -> (Sch, f64) {
    let mut rng = Rng(seed);
    let mut s = start.clone();
    s.balance();
    let mut om = weights(s.r, &mut rng);
    let (mut delta, mut eta, mut stall) = (1e-2, o.kick, 0);
    let nmax = o.bound * s.norms2().iter().cloned().fold(0.0f64, f64::max);
    let t0 = Instant::now();
    for it in 0..o.steps {
        let Some(pr) = Proj::new(&s) else { break };
        let (phi, mut d, gp) = potential(&s, &om, delta, true);
        let x = s.x();
        let mut dir = pr.moduli(&gp);
        for v in dir.iter_mut() { *v = -*v; }
        let mut kicked = false;
        if sq(&dir).sqrt() < 1e-7 * (1.0 + sq(&gp).sqrt()) || stall >= 2 || eta < 1e-3 {
            let v: Vec<f64> = (0..x.len()).map(|_| rng.normal()).collect();
            dir = pr.moduli(&v);
            kicked = true; stall = 0; eta = o.kick;
        }
        let dn = sq(&dir).sqrt();
        if dn < 1e-12 { if !o.quiet { println!("{tag} step {it}: rigid at {} products (no moduli)", s.r); } break; }
        let len = sq(&x).sqrt() / (s.r as f64).sqrt() / dn;
        let mut moved = false;
        for _ in 0..8 {
            let x2: Vec<f64> = x.iter().zip(&dir).map(|(a, b)| a + eta * len * b).collect();
            let mut s2 = s.with_x(&x2);
            if polish(&mut s2, t, 60, 1e-13) < 1e-10 {
                s2.balance();
                if s2.norms2().iter().cloned().fold(0.0f64, f64::max) <= nmax {
                    let (phi2, d2, _) = potential(&s2, &om, delta, false);
                    if kicked || phi2 < phi { s = s2; d = d2; moved = true; if !kicked { eta = (eta * 1.5).min(1.0); } break; }
                }
            }
            eta *= 0.5;
        }
        if !moved { stall += 1; eta = o.kick; }
        while let Some(m) = merge(&s, &d, t, 1e-4) {
            s = m;
            om = weights(s.r, &mut rng);
            d = potential(&s, &om, delta, false).1;
            println!("{tag} step {it}: merged a pair -> {} products ({:.0} s)", s.r, t0.elapsed().as_secs_f64());
        }
        delta = (delta * 0.9f64).max(1e-7);
        if !o.quiet && it % 20 == 0 {
            let (ker, triv) = pr.dimensions(&mut rng, (pr.triv.len() + 80).min(pr.n));
            let mut ds: Vec<f64> = Vec::new();
            for a in 0..s.r { for b in a + 1..s.r { ds.push(d[a * s.r + b]); } }
            ds.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let n2 = s.norms2();
            println!("{tag} step {it}: {} products, moduli {}, min D {:.5} {:.5}, norms {:.1}..{:.1}, eta {:.2e}{} ({:.0} s)", s.r,
                     ker as i64 - triv as i64, ds[0], ds[1.min(ds.len() - 1)], n2.iter().cloned().fold(f64::MAX, f64::min),
                     n2.iter().cloned().fold(0.0f64, f64::max), eta, if kicked { " kick" } else { "" }, t0.elapsed().as_secs_f64());
        }
    }
    let f = polish(&mut s, t, 300, 1e-14);
    (s, f)
}

/// Regularized Levenberg-Marquardt from any start (the numerical search of Tichavsky, Phan and
/// Cichocki for difficult tensors, in a plain form): minimize 1/2 |F|^2 + mu/2 |x|^2, mu lowered
/// by a factor 4 whenever the cost has not fallen by 2% in `window` iterations and dropped at the
/// end; at mu = 0 the next stall ends the run.  The penalty keeps the products bounded while the
/// residual is large (without it the iteration runs into degenerations, pairs of products that
/// cancel with diverging norms: border rank, not rank); a run whose products outgrow nmax is
/// abandoned.  (A variant that steers mu to hold |x|^2 under a fixed bound did worse: <3x3x3:23>
/// from 23 of 40 starts against 32, <3x3x4:29> from 0 of 320 against 2 of 40.)
/// Returns (max |F|, largest product norm^2, iterations, final mu).
fn lm_search(s: &mut Sch, t: &[f64], iters: usize, mu0: f64, nmax: f64, window: usize) -> (f64, f64, usize, f64) {
    let n = s.n();
    let (mut mu, mut lam) = (mu0, 1e-3);
    let mut res = residual(s, t);
    let mut x = s.x();
    let mut cost = 0.5 * sq(&res) + 0.5 * mu * sq(&x);
    let (mut mark, mut mark_it) = (cost, 0usize);
    let mut it = 0;
    while it < iters {
        it += 1;
        if res.iter().fold(0.0f64, |m, v| m.max(v.abs())) < 1e-12 { break; }
        if s.norms2().iter().cloned().fold(0.0f64, f64::max) > nmax { break; }
        let nm = normal(s);
        let mut g = grad_f(s, &res);
        for (gi, xi) in g.iter_mut().zip(&x) { *gi += mu * xi; }
        let scale = (0..n).map(|i| nm[i * n + i]).fold(0.0f64, f64::max).max(1e-300);
        let mut moved = false;
        for _ in 0..10 {
            let mut a = nm.clone();
            if !factor(&mut a, n, mu + lam * scale) { lam *= 10.0; continue; }
            let mut d: Vec<f64> = g.iter().map(|v| -v).collect();
            solve(&a, n, &mut d);
            let x2: Vec<f64> = x.iter().zip(&d).map(|(a, b)| a + b).collect();
            let s2 = s.with_x(&x2);
            let r2 = residual(&s2, t);
            let c2 = 0.5 * sq(&r2) + 0.5 * mu * sq(&x2);
            if c2 < cost && c2.is_finite() { *s = s2; x = x2; res = r2; cost = c2; lam = (lam / 3.0).max(1e-12); moved = true; break; }
            lam *= 4.0;
        }
        let full = it - mark_it >= window;
        let stalled = !moved || (full && cost > 0.98 * mark);
        if full { mark = cost; mark_it = it; }
        if stalled {
            if mu == 0.0 { break; }
            mu = if mu > 1e-9 { mu * 0.25 } else { 0.0 };
            cost = 0.5 * sq(&res) + 0.5 * mu * sq(&x);
            mark = cost; mark_it = it; lam = lam.max(1e-6);
        }
    }
    (res.iter().fold(0.0f64, |m, v| m.max(v.abs())), s.norms2().iter().cloned().fold(0.0f64, f64::max), it, mu)
}

/// One Levenberg-Marquardt step on the free entries of 1/2 |F|^2 + mu/2 sum_i w_i x_i^2; true if it moved.
fn step_free(s: &mut Sch, t: &[f64], x: &mut Vec<f64>, fixed: &[bool], w: &[f64], mu: f64, lam: &mut f64) -> bool {
    let n = s.n();
    let res = residual(s, t);
    let pen = |x: &[f64]| -> f64 { x.iter().zip(w).map(|(v, w)| w * v * v).sum::<f64>() };
    let cost = 0.5 * sq(&res) + 0.5 * mu * pen(x);
    let nm = normal(s);
    let gf = grad_f(s, &res);
    let free: Vec<usize> = (0..n).filter(|i| !fixed[*i]).collect();
    let nf = free.len();
    if nf == 0 { return false; }
    let scale = free.iter().map(|&i| nm[i * n + i]).fold(0.0f64, f64::max).max(1e-300);
    let mut sub = vec![0.0; nf * nf];
    for (a, &i) in free.iter().enumerate() { let row = &nm[i * n..(i + 1) * n]; let out = &mut sub[a * nf..(a + 1) * nf]; for (b, &j) in free.iter().enumerate() { out[b] = row[j]; } }
    for _ in 0..10 {
        let mut a = sub.clone();
        for (q, &i) in free.iter().enumerate() { a[q * nf + q] += mu * w[i]; }
        if !factor(&mut a, nf, *lam * scale) { *lam *= 10.0; continue; }
        let mut d: Vec<f64> = free.iter().map(|&i| -(gf[i] + mu * w[i] * x[i])).collect();
        solve(&a, nf, &mut d);
        let mut x2 = x.clone();
        for (q, &i) in free.iter().enumerate() { x2[i] += d[q]; }
        let s2 = s.with_x(&x2);
        let c2 = 0.5 * sq(&residual(&s2, t)) + 0.5 * mu * pen(&x2);
        if c2 < cost && c2.is_finite() { *s = s2; *x = x2; *lam = (*lam / 3.0).max(1e-12); return true; }
        *lam *= 4.0;
    }
    false
}

fn fmax_of(s: &Sch, t: &[f64]) -> f64 { residual(s, t).iter().fold(0.0f64, |m, v| m.max(v.abs())) }

/// Clamping (after Smirnov's practice): from a numerically exact scheme at a generic point of its
/// orbit to a sparse one.  Rounds of (1) pressure: a few steps under the log-sum sparsity penalty
/// mu/2 sum_i w_i x_i^2, w_i = eps^2 / (x_i^2 + eps^2), which slides the point along the orbit
/// toward small entries; (2) clamp: the smallest entries beside the largest of their factor vector,
/// a few at a time, are set to zero and frozen; (3) restore: steps with mu = 0 on the free entries
/// until |F| is back under 1e-10, or the clamp is undone and those entries are left alone for good.
/// Returns (entries frozen at zero, rounds).  The scheme stays exact throughout.
fn sparsify(s: &mut Sch, t: &[f64], rounds: usize, clamp: f64) -> (usize, usize) {
    let n = s.n();
    let (ni, nj, nk) = s.dims(); let r = s.r;
    s.balance();
    let mut x = s.x();
    let (mut fixed, mut protected) = (vec![false; n], vec![false; n]);
    let (mut eps, mut lam) = (0.3f64, 1e-4);
    let mut rd = 0;
    while rd < rounds {
        rd += 1;
        let w: Vec<f64> = x.iter().zip(&fixed).map(|(v, f)| if *f { 0.0 } else { eps * eps / (v * v + eps * eps) }).collect();
        for _ in 0..6 { if !step_free(s, t, &mut x, &fixed, &w, 1e-3, &mut lam) { break; } }
        let mut cand: Vec<(f64, usize)> = Vec::new();
        for (off, d) in [(0, ni), (r * ni, nj), (r * (ni + nj), nk)] {
            for p in 0..r {
                let big = x[off + p * d..off + (p + 1) * d].iter().fold(0.0f64, |m, v| m.max(v.abs()));
                for i in off + p * d..off + (p + 1) * d { if !fixed[i] && !protected[i] && x[i].abs() < clamp * big { cand.push((x[i].abs() / big.max(1e-300), i)); } }
            }
        }
        cand.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        let nfree = fixed.iter().filter(|f| !**f).count();
        cand.truncate((nfree / 40).max(1));
        let (xc, fc, sc) = (x.clone(), fixed.clone(), s.clone());
        for c in &cand { x[c.1] = 0.0; fixed[c.1] = true; }
        *s = s.with_x(&x);
        let zero = vec![0.0; n];
        let mut ok = false;
        let mut l2 = 1e-6;
        for _ in 0..80 {
            if fmax_of(s, t) < 1e-10 { ok = true; break; }
            if !step_free(s, t, &mut x, &fixed, &zero, 0.0, &mut l2) { break; }
        }
        if !ok && fmax_of(s, t) < 1e-10 { ok = true; }
        if !ok {                                // undo: back to the exact scheme before the clamp (and before the pressure)
            if cand.is_empty() { *s = sc; x = xc; fixed = fc; } else { *s = sc; x = xc; fixed = fc; for c in &cand { protected[c.1] = true; } }
        }
        if cand.is_empty() { if eps <= 0.021 { break; } eps = (eps * 0.7).max(0.02); }
    }
    (fixed.iter().filter(|f| **f).count(), rd)
}

/// Read a sparse scheme as rational.  A sparse point still has a torus of equivalent points with the
/// same zeros: the rescalings of the products and the diagonal matrices of the group (A -> D_a A
/// D_b^-1, B -> D_b B D_c^-1, C -> D_a^-1 C D_c).  In logarithms of the absolute values these act
/// linearly, so the torus element that brings the most entries to +-1 is a robust linear fit
/// (iteratively reweighted least squares toward log |x| = 0).  After it, if every entry is within
/// 1e-6 of a multiple of 1/den for den in {1, 2, 4, 8}, the entries are rounded and the Brent
/// equations verified exactly in integers; returns that den.
fn rationalize(s: &mut Sch, t: &[f64]) -> Option<i64> {
    let (ni, nj, nk) = s.dims(); let r = s.r; let g = s.g;
    // unknowns: lu_t (r), lv_t (r), alpha_i (g0), beta_j (g1), gamma_k (g2)
    let nu = 2 * r + g[0] + g[1] + g[2];
    let (oa, ob, oc) = (2 * r, 2 * r + g[0], 2 * r + g[0] + g[1]);
    let mut rows: Vec<(Vec<(usize, f64)>, f64)> = Vec::new();      // sparse row, right-hand side: row . z = -log|x|
    for p in 0..r {
        for i in 0..g[0] { for j in 0..g[1] { let v = s.u[p * ni + i * g[1] + j]; if v != 0.0 { rows.push((vec![(p, 1.0), (oa + i, 1.0), (ob + j, -1.0)], -v.abs().ln())); } } }
        for j in 0..g[1] { for k in 0..g[2] { let v = s.v[p * nj + j * g[2] + k]; if v != 0.0 { rows.push((vec![(r + p, 1.0), (ob + j, 1.0), (oc + k, -1.0)], -v.abs().ln())); } } }
        for i in 0..g[0] { for k in 0..g[2] { let v = s.w[p * nk + i * g[2] + k]; if v != 0.0 { rows.push((vec![(p, -1.0), (r + p, -1.0), (oa + i, -1.0), (oc + k, 1.0)], -v.abs().ln())); } } }
    }
    let mut z = vec![0.0; nu];
    let mut wt = vec![1.0; rows.len()];
    for _ in 0..30 {
        let mut m = vec![0.0; nu * nu];
        let mut rhs = vec![0.0; nu];
        for ((row, b), w) in rows.iter().zip(&wt) {
            for &(a, ca) in row { rhs[a] += w * ca * b; for &(c, cc) in row { m[a * nu + c] += w * ca * cc; } }
        }
        if !factor(&mut m, nu, 1e-9) { return None; }
        solve(&m, nu, &mut rhs);
        z = rhs;
        for (q, (row, b)) in rows.iter().enumerate() {
            let e: f64 = row.iter().map(|&(a, c)| c * z[a]).sum::<f64>() - b;
            wt[q] = 1.0 / (e.abs() + 1e-4);
        }
    }
    let mut q = s.clone();
    for p in 0..r {
        for i in 0..g[0] { for j in 0..g[1] { q.u[p * ni + i * g[1] + j] *= (z[p] + z[oa + i] - z[ob + j]).exp(); } }
        for j in 0..g[1] { for k in 0..g[2] { q.v[p * nj + j * g[2] + k] *= (z[r + p] + z[ob + j] - z[oc + k]).exp(); } }
        for i in 0..g[0] { for k in 0..g[2] { q.w[p * nk + i * g[2] + k] *= (-z[p] - z[r + p] - z[oa + i] + z[oc + k]).exp(); } }
    }
    if fmax_of(&q, t) > 1e-8 { return None; }
    for den in [1i64, 2, 4, 8] {
        let d = den as f64;
        if q.u.iter().chain(&q.v).chain(&q.w).all(|v| ((v * d).round() - v * d).abs() < 1e-6) {
            let int = |x: &[f64]| -> Vec<i64> { x.iter().map(|v| (v * d).round() as i64).collect() };
            let (u, v, w) = (int(&q.u), int(&q.v), int(&q.w));
            let mut exact = true;       // sum_p u v w = den^3 T, in integers
            'chk: for a in 0..ni { for b in 0..nj { for c in 0..nk {
                let mut acc = 0i64;
                for p in 0..r { acc += u[p * ni + a] * v[p * nj + b] * w[p * nk + c]; }
                if acc != den * den * den * (t[(a * nj + b) * nk + c] as i64) { exact = false; break 'chk; }
            } } }
            if exact {
                s.u = u.iter().map(|v| *v as f64 / d).collect(); s.v = v.iter().map(|v| *v as f64 / d).collect(); s.w = w.iter().map(|v| *v as f64 / d).collect();
                return Some(den);
            }
        }
    }
    *s = q;         // keep the normalized point
    None
}

/// The second half of clamping: a sparse scheme whose nonzero entries are not all simple still has
/// freedom (the torus, and the scheme's moduli).  After rationalize's normalization, the free entry
/// nearest to one of +-1, +-1/2, +-2 is set to it and frozen, and the others are re-solved with
/// mu = 0 until |F| is back under 1e-10 -- or the entry is released for good.  Repeated until no
/// free entry is within 0.25 of a simple value.  Returns the number of entries so fixed.
fn discretize(s: &mut Sch, t: &[f64]) -> usize {
    let n = s.n();
    let mut x = s.x();
    let mut fixed: Vec<bool> = x.iter().map(|v| *v == 0.0).collect();
    let mut protected = vec![false; n];
    let zero = vec![0.0; n];
    let cands = [1.0, -1.0, 0.5, -0.5, 2.0, -2.0];
    let mut done = 0;
    loop {
        let mut best: Option<(f64, usize, f64)> = None;
        for i in 0..n {
            if fixed[i] || protected[i] { continue; }
            for &c in &cands { let d = (x[i] - c).abs(); if d < 0.25 && best.map_or(true, |b| d < b.0) { best = Some((d, i, c)); } }
        }
        let Some((_, i, c)) = best else { break };
        let (xc, sc) = (x.clone(), s.clone());
        x[i] = c; fixed[i] = true;
        *s = s.with_x(&x);
        let mut lam = 1e-6;
        let mut ok = fmax_of(s, t) < 1e-10;
        for _ in 0..60 {
            if ok { break; }
            if !step_free(s, t, &mut x, &fixed, &zero, 0.0, &mut lam) { break; }
            ok = fmax_of(s, t) < 1e-10;
        }
        if ok { done += 1; } else { x = xc; *s = sc; fixed[i] = false; protected[i] = true; }
    }
    done
}

/// Schemes with a prescribed symmetry.  A group element g of order q acts on the three factor
/// spaces by matrices MA, MB, MC (A -> X A Y^-1 and so on; autgroup.py writes them).  A g-invariant
/// scheme is m orbits {g^j (u, v, w) : j < q} and f products fixed by g, whose factors lie in the
/// fixed subspaces of MA, MB, MC; its unknowns are the m representatives and the coordinates of the
/// fixed products, x_red, and the full scheme is x = P x_red with P linear.  So the search is the
/// same Levenberg-Marquardt on J P: normal matrix P^T N P, gradient P^T J^T F -- with a third of
/// the unknowns for q = 3 (the equations are g-invariant too, so nothing is lost).
struct Sym { q: usize, m: usize, f: usize, g: [usize; 3], nred: usize, rows: Vec<Vec<(usize, f64)>>,
             fixb: Vec<[Vec<Vec<f64>>; 3]>, foff: Vec<usize> }   // per fixed product: bases of its three eigenspaces, and its offset in x_red

fn matmul_sq(a: &[f64], b: &[f64], d: usize) -> Vec<f64> {
    let mut c = vec![0.0; d * d];
    for i in 0..d { for k in 0..d { let v = a[i * d + k]; if v != 0.0 { for j in 0..d { c[i * d + j] += v * b[k * d + j]; } } } }
    c
}

impl Sym {
    /// fs: per fixed product, the signs (+1 or -1) with which g acts on its three factors (their
    /// product must be +1; for odd q only +1 +1 +1): the factors lie in those eigenspaces
    fn new(g: [usize; 3], q: usize, acts: [Vec<f64>; 3], m: usize, fs: &[[f64; 3]]) -> Sym {
        let dims = [g[0] * g[1], g[1] * g[2], g[0] * g[2]];
        let f = fs.len();
        // powers of each action; the eigenspace for sign s is the image of the average of s^j M^j
        let mut pw: Vec<Vec<Vec<f64>>> = Vec::new();
        for s in 0..3 {
            let d = dims[s];
            let mut id = vec![0.0; d * d]; for i in 0..d { id[i * d + i] = 1.0; }
            let mut p = vec![id];
            for j in 1..q { let nx = matmul_sq(&p[j - 1], &acts[s], d); p.push(nx); }
            let back = matmul_sq(&p[q - 1], &acts[s], d);
            assert!((0..d * d).all(|i| (back[i] - p[0][i]).abs() < 1e-7), "the action does not have order q");
            pw.push(p);
        }
        let eig = |s: usize, sign: f64| -> Vec<Vec<f64>> {
            let d = dims[s];
            let cols: Vec<Vec<f64>> = (0..d).map(|c| (0..d).map(|r| pw[s].iter().enumerate().map(|(j, m)| sign.powi(j as i32) * m[r * d + c]).sum::<f64>() / q as f64).collect()).collect();
            orthonormalize(cols, 1e-7)
        };
        let fixb: Vec<[Vec<Vec<f64>>; 3]> = fs.iter().map(|sg| { assert!(sg[0] * sg[1] * sg[2] > 0.0 && (q % 2 == 0 || sg.iter().all(|x| *x > 0.0)), "fixed-product signs"); [eig(0, sg[0]), eig(1, sg[1]), eig(2, sg[2])] }).collect();
        let per = dims[0] + dims[1] + dims[2];
        let r = q * m + f;
        let n = r * per;
        let mut foff = Vec::new();
        let mut nred = m * per;
        for b in &fixb { foff.push(nred); nred += b[0].len() + b[1].len() + b[2].len(); }
        let offs_full = [0, r * dims[0], r * (dims[0] + dims[1])];
        let offs_red = [0, dims[0], dims[0] + dims[1]];
        let mut rows: Vec<Vec<(usize, f64)>> = vec![Vec::new(); n];
        for o in 0..m { for j in 0..q { let t = o * q + j; for s in 0..3 { let d = dims[s];
            for a in 0..d { let row = &mut rows[offs_full[s] + t * d + a];
                for b in 0..d { let c = pw[s][j][a * d + b]; if c.abs() > 1e-13 { row.push((o * per + offs_red[s] + b, c)); } } }
        } } }
        for fi in 0..f { let t = q * m + fi; let mut off = foff[fi]; for s in 0..3 { let d = dims[s];
            for a in 0..d { let row = &mut rows[offs_full[s] + t * d + a];
                for (e, bv) in fixb[fi][s].iter().enumerate() { if bv[a].abs() > 1e-13 { row.push((off + e, bv[a])); } } }
            off += fixb[fi][s].len();
        } }
        Sym { q, m, f, g, nred, rows, fixb, foff }
    }
    fn expand(&self, x: &[f64]) -> Sch {
        let full: Vec<f64> = self.rows.iter().map(|row| row.iter().map(|&(i, c)| c * x[i]).sum()).collect();
        let r = self.q * self.m + self.f;
        Sch { g: self.g, r, u: vec![], v: vec![], w: vec![] }.with_x(&full)
    }
    fn reduce_vec(&self, y: &[f64]) -> Vec<f64> {
        let mut out = vec![0.0; self.nred];
        for (k, row) in self.rows.iter().enumerate() { for &(i, c) in row { out[i] += c * y[k]; } }
        out
    }
    /// P^T N P
    fn reduce_mat(&self, nm: &[f64]) -> Vec<f64> {
        let (n, nr) = (self.rows.len(), self.nred);
        let mut np = vec![0.0; n * nr];
        for i in 0..n {
            let (src, dst) = (&nm[i * n..(i + 1) * n], &mut np[i * nr..(i + 1) * nr]);
            for k in 0..n { let v = src[k]; if v != 0.0 { for &(ri, c) in &self.rows[k] { dst[ri] += v * c; } } }
        }
        let mut out = vec![0.0; nr * nr];
        for i in 0..n { let src = &np[i * nr..(i + 1) * nr];
            for &(ri, c) in &self.rows[i] { let dst = &mut out[ri * nr..(ri + 1) * nr]; for k in 0..nr { dst[k] += c * src[k]; } } }
        out
    }
}

/// lm_search in the reduced unknowns of a symmetry; returns (scheme, max |F|, largest product norm^2, iterations).
/// With cmax > 0 it is the constrained search of Tichavsky, Phan and Cichocki instead: minimize
/// 1/2 |F|^2 subject to |x|^2 <= cmax, no penalty.  A step that would leave the ball is replaced
/// by the minimizer of the damped model on the sphere: (N + lam + nu) d = -(J^T F + nu x) with the
/// multiplier nu found by bisection so that |x + d|^2 = cmax (each trial one Cholesky).
fn lm_sym(sy: &Sym, x0: Vec<f64>, t: &[f64], iters: usize, mu0: f64, nmax: f64, window: usize, cmax: f64) -> (Sch, f64, f64, usize) {
    let nr = sy.nred;
    let (mut mu, mut lam) = (if cmax > 0.0 { 0.0 } else { mu0 }, 1e-3);
    let mut x = x0;
    if cmax > 0.0 && sq(&x) > cmax { let c = (cmax / sq(&x)).sqrt(); for v in x.iter_mut() { *v *= c; } }
    let mut s = sy.expand(&x);
    let mut res = residual(&s, t);
    let mut cost = 0.5 * sq(&res) + 0.5 * mu * sq(&x);
    let (mut mark, mut mark_it) = (cost, 0usize);
    let mut it = 0;
    while it < iters {
        it += 1;
        if res.iter().fold(0.0f64, |m, v| m.max(v.abs())) < 1e-12 { break; }
        if s.norms2().iter().cloned().fold(0.0f64, f64::max) > nmax { break; }
        let nm = sy.reduce_mat(&normal(&s));
        let mut g = sy.reduce_vec(&grad_f(&s, &res));
        for (gi, xi) in g.iter_mut().zip(&x) { *gi += mu * xi; }
        let scale = (0..nr).map(|i| nm[i * nr + i]).fold(0.0f64, f64::max).max(1e-300);
        let mut moved = false;
        for _ in 0..10 {
            let step = |nu: f64| -> Option<Vec<f64>> {
                let mut a = nm.clone();
                if !factor(&mut a, nr, mu + lam * scale + nu) { return None; }
                let mut d: Vec<f64> = g.iter().zip(&x).map(|(gv, xv)| -(gv + nu * xv)).collect();
                solve(&a, nr, &mut d);
                Some(d)
            };
            let Some(mut d) = step(0.0) else { lam *= 10.0; continue };
            let norm_after = |d: &[f64]| -> f64 { x.iter().zip(d).map(|(a, b)| (a + b) * (a + b)).sum() };
            if cmax > 0.0 && norm_after(&d) > cmax * (1.0 + 1e-9) {
                let (mut lo, mut hi) = (0.0f64, 1e-6 * scale);
                let mut dh = None;
                for _ in 0..40 { match step(hi) { Some(c) if norm_after(&c) <= cmax => { dh = Some(c); break; } _ => { lo = hi; hi *= 8.0; } } }
                if let Some(mut best) = dh {
                    for _ in 0..8 {
                        let mid = if lo > 0.0 { (lo * hi).sqrt() } else { hi * 0.25 };
                        match step(mid) { Some(c) if norm_after(&c) <= cmax => { hi = mid; best = c; } _ => { lo = mid; } }
                    }
                    d = best;
                } else { lam *= 10.0; continue; }
            }
            let x2: Vec<f64> = x.iter().zip(&d).map(|(a, b)| a + b).collect();
            let s2 = sy.expand(&x2);
            let r2 = residual(&s2, t);
            let c2 = 0.5 * sq(&r2) + 0.5 * mu * sq(&x2);
            if c2 < cost && c2.is_finite() { s = s2; x = x2; res = r2; cost = c2; lam = (lam / 3.0).max(1e-12); moved = true; break; }
            lam *= 4.0;
        }
        let full = it - mark_it >= window;
        let stalled = !moved || (full && cost > 0.98 * mark);
        if full { mark = cost; mark_it = it; }
        if stalled {
            if mu == 0.0 { break; }
            mu = if mu > 1e-9 { mu * 0.25 } else { 0.0 };
            cost = 0.5 * sq(&res) + 0.5 * mu * sq(&x);
            mark = cost; mark_it = it; lam = lam.max(1e-6);
        }
    }
    let (f, nm) = (res.iter().fold(0.0f64, |m, v| m.max(v.abs())), s.norms2().iter().cloned().fold(0.0f64, f64::max));
    (s, f, nm, it)
}

fn random_scheme(g: [usize; 3], r: usize, sigma: f64, rng: &mut Rng) -> Sch {
    let (ni, nj, nk) = (g[0] * g[1], g[1] * g[2], g[0] * g[2]);
    let mut f = |len: usize| -> Vec<f64> { (0..len).map(|_| sigma * rng.normal()).collect() };
    Sch { g, r, u: f(r * ni), v: f(r * nj), w: f(r * nk) }
}

/// a known scheme with `drop` products removed (the run's index picks which) and noise added
fn warm_scheme(s0: &Sch, drop: usize, noise: f64, k: usize, rng: &mut Rng) -> Sch {
    let (ni, nj, nk) = s0.dims();
    let mut gone = vec![false; s0.r];
    gone[k % s0.r] = true;
    let mut left = drop - 1;
    while left > 0 { let q = (rng.next() % s0.r as u64) as usize; if !gone[q] { gone[q] = true; left -= 1; } }
    let keep = |x: &[f64], d: usize| -> Vec<f64> { (0..s0.r).filter(|q| !gone[*q]).flat_map(|q| x[q * d..(q + 1) * d].to_vec()).collect() };
    let mut s = Sch { g: s0.g, r: s0.r - drop, u: keep(&s0.u, ni), v: keep(&s0.v, nj), w: keep(&s0.w, nk) };
    s.balance();
    let rms = (sq(&s.x()) / s.n() as f64).sqrt();
    for x in s.u.iter_mut().chain(s.v.iter_mut()).chain(s.w.iter_mut()) { *x += noise * rms * rng.normal(); }
    s
}

fn trivial(g: [usize; 3]) -> Sch {
    let (ni, nj, nk) = (g[0] * g[1], g[1] * g[2], g[0] * g[2]);
    let r = g[0] * g[1] * g[2];
    let (mut u, mut v, mut w) = (vec![0.0; r * ni], vec![0.0; r * nj], vec![0.0; r * nk]);
    let mut t = 0;
    for i in 0..g[0] { for j in 0..g[1] { for k in 0..g[2] {
        u[t * ni + i * g[1] + j] = 1.0; v[t * nj + j * g[2] + k] = 1.0; w[t * nk + i * g[2] + k] = 1.0; t += 1;
    } } }
    Sch { g, r, u, v, w }
}

fn num(v: &Value) -> f64 {
    if let Some(x) = v.as_f64() { return x; }
    let s = v.as_str().expect("a number or a fraction string");
    match s.split_once('/') { Some((a, b)) => a.trim().parse::<f64>().unwrap() / b.trim().parse::<f64>().unwrap(), None => s.trim().parse().unwrap() }
}

fn load(path: &str) -> Sch {
    if let Some(shape) = path.strip_prefix("trivial:") {
        let g: Vec<usize> = shape.split('x').map(|x| x.parse().unwrap()).collect();
        return trivial([g[0], g[1], g[2]]);
    }
    let d: Value = serde_json::from_str(&std::fs::read_to_string(path).expect("scheme file")).expect("JSON");
    let g: Vec<usize> = d["n"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as usize).collect();
    let g = [g[0], g[1], g[2]];
    let mat = |k: &str| -> Vec<f64> { d[k].as_array().unwrap().iter().flat_map(|row| row.as_array().unwrap().iter().map(num).collect::<Vec<_>>()).collect() };
    let r = d["u"].as_array().unwrap().len();
    let mut s = Sch { g, r, u: mat("u"), v: mat("v"), w: mat("w") };
    let t = tensor(g);
    if residual(&s, &t).iter().fold(0.0f64, |m, x| m.max(x.abs())) > 1e-9 {     // C given as (k, i): reorder to (i, k)
        let nk = g[0] * g[2];
        let mut w2 = vec![0.0; r * nk];
        for p in 0..r { for i in 0..g[0] { for k in 0..g[2] { w2[p * nk + i * g[2] + k] = s.w[p * nk + k * g[0] + i]; } } }
        s.w = w2;
        assert!(residual(&s, &t).iter().fold(0.0f64, |m, x| m.max(x.abs())) < 1e-9, "not a scheme in either orientation of C");
    }
    s
}

fn save(s: &Sch, f: f64, path: &str) {
    let (ni, nj, nk) = s.dims();
    let rows = |x: &[f64], d: usize| -> Vec<Vec<f64>> { x.chunks(d).map(|c| c.to_vec()).collect() };
    let v = serde_json::json!({"n": s.g, "m": s.r, "max_residual": f, "u": rows(&s.u, ni), "v": rows(&s.v, nj), "w": rows(&s.w, nk)});
    std::fs::write(path, serde_json::to_string(&v).unwrap()).expect("write");
}

fn main() {
    let a: Vec<String> = std::env::args().skip(1).collect();
    if a.is_empty() { eprintln!("usage: vdescend SCHEME [--runs R] [--steps N] [--seed S] [--threads T] [--kick K] [--bound B] [--out DIR] [--moduli] [--quiet]"); std::process::exit(2); }
    let opt = |k: &str, d: f64| -> f64 { a.iter().position(|x| x == k).map(|i| a[i + 1].parse().unwrap()).unwrap_or(d) };
    let (runs, seed, threads) = (opt("--runs", 8.0) as usize, opt("--seed", 1.0) as u64, opt("--threads", 8.0) as usize);
    let o = Opts { steps: opt("--steps", 300.0) as usize, kick: opt("--kick", 0.3), bound: opt("--bound", 30.0), quiet: a.iter().any(|x| x == "--quiet") };
    let out = a.iter().position(|x| x == "--out").map(|i| a[i + 1].clone());
    unsafe { std::env::set_var("VECLIB_MAXIMUM_THREADS", if a.iter().any(|x| x == "--moduli") { "8" } else { "1" }); }
    let s0 = load(&a[0]);
    let t = tensor(s0.g);
    let name = a[0].rsplit('/').next().unwrap().to_string();
    if a.iter().any(|x| x == "--moduli") {
        let mut b = s0.clone(); b.balance();
        let pr = Proj::new(&b).expect("normal matrix");
        let (ker, triv) = pr.dimensions(&mut Rng(seed), (pr.triv.len() + 200).min(pr.n));
        println!("{name}: <{}x{}x{}:{}>  unknowns {}  tangent space {}  rescalings + group orbit {}  MODULI {}", s0.g[0], s0.g[1], s0.g[2], s0.r, s0.n(), ker, triv, ker as i64 - triv as i64);
        return;
    }
    let pool = rayon::ThreadPoolBuilder::new().num_threads(threads).build().unwrap();
    let t0 = Instant::now();
    let (search, warm) = (opt("--search", 0.0) as usize, opt("--warm", 0.0) as usize);
    if let Some(i) = a.iter().position(|x| x == "--sym") {
        // the search among schemes invariant under a group element: m orbits and f fixed products
        let d: Value = if a[i + 1] == "id" {       // no symmetry: one element, the identity (the plain problem through the same code)
            let idm = |n: usize| -> Vec<Vec<f64>> { (0..n).map(|r| (0..n).map(|c| if r == c { 1.0 } else { 0.0 }).collect()).collect() };
            let (ni, nj, nk) = s0.dims();
            serde_json::json!([{"order": 1, "perm": (0..s0.r).collect::<Vec<_>>(), "MA": idm(ni), "MB": idm(nj), "MC": idm(nk)}])
        } else { serde_json::from_str(&std::fs::read_to_string(&a[i + 1]).expect("symmetry file")).expect("JSON") };
        let els = d.as_array().unwrap();
        let q_want = if a[i + 1] == "id" { 1 } else { opt("--order", 3.0) as u64 };
        let ei = a.iter().position(|x| x == "--elem").map(|j| a[j + 1].parse::<usize>().unwrap())
            .unwrap_or_else(|| els.iter().position(|e| e["order"].as_u64() == Some(q_want)).expect("no element of that order"));
        let e = &els[ei];
        let q = e["order"].as_u64().unwrap() as usize;
        let mat = |k: &str| -> Vec<f64> { e[k].as_array().unwrap().iter().flat_map(|row| row.as_array().unwrap().iter().map(num).collect::<Vec<_>>()).collect() };
        let (m, f) = (opt("--orbits", 18.0) as usize, opt("--fixed", 0.0) as usize);
        // --fsigns ppp,pmm,...: the sign types of the fixed products, repeated as needed (default ppp)
        let types: Vec<[f64; 3]> = a.iter().position(|x| x == "--fsigns").map(|j| a[j + 1].split(',').map(|w| { let c: Vec<f64> = w.chars().map(|ch| if ch == 'm' { -1.0 } else { 1.0 }).collect(); [c[0], c[1], c[2]] }).collect())
            .unwrap_or_else(|| vec![[1.0, 1.0, 1.0]]);
        let fs: Vec<[f64; 3]> = (0..f).map(|i| types[i % types.len()]).collect();
        let sy = Sym::new(s0.g, q, [mat("MA"), mat("MB"), mat("MC")], m, &fs);
        let (iters, mu0, sigma, nmax, window) = (opt("--iters", 2000.0) as usize, opt("--mu", 1e-2), opt("--init", 0.5), opt("--nmax", 1e4), opt("--window", 60.0) as usize);
        let target = q * m + f;
        // --cnorm c: the constrained search, |x_red|^2 <= c per product of the full scheme / q ... given per product: c * rank / q
        let cnorm = opt("--cnorm", 0.0) / q as f64;
        // the symmetry must fix the tensor: the classical algorithm's image under one orbit sum would show otherwise; check on a random point
        println!("# {name}: <{}x{}x{}> rank {target} = {m} orbits of {q} + {f} fixed, element {ei} of {}, {} unknowns (of {}), {runs} random starts (sigma {sigma}) from seed {seed}, at most {iters} iterations, {threads} threads",
                 s0.g[0], s0.g[1], s0.g[2], a[i + 1].rsplit('/').next().unwrap(), sy.nred, sy.rows.len());
        // --symwarm D: starts from the loaded scheme (which must have this symmetry): its orbits' representatives
        // less D orbits (the run's index picks the first), plus noise; the fixed products start at random
        let symwarm = a.iter().position(|x| x == "--symwarm").map(|j| a[j + 1].parse::<usize>().unwrap());
        let noise = opt("--noise", 0.1);
        let mut reps: Vec<Vec<f64>> = Vec::new();
        let mut known_fixed: Vec<[Vec<f64>; 3]> = Vec::new();     // the loaded scheme's products fixed by g
        if symwarm.is_some() {
            let perm: Vec<usize> = e["perm"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as usize).collect();
            let (ni, nj, nk) = s0.dims();
            for t in 0..s0.r { if perm[t] == t { known_fixed.push([s0.u[t * ni..(t + 1) * ni].to_vec(), s0.v[t * nj..(t + 1) * nj].to_vec(), s0.w[t * nk..(t + 1) * nk].to_vec()]); } }
        }
        if symwarm.is_some() {
            let perm: Vec<usize> = e["perm"].as_array().unwrap().iter().map(|v| v.as_u64().unwrap() as usize).collect();
            let (ni, nj, nk) = s0.dims();
            let mut seen = vec![false; s0.r];
            for t in 0..s0.r {
                if seen[t] { continue; }
                let (mut len, mut c) = (0, t);
                while !seen[c] { seen[c] = true; c = perm[c]; len += 1; }
                if len == q { let mut v = s0.u[t * ni..(t + 1) * ni].to_vec(); v.extend_from_slice(&s0.v[t * nj..(t + 1) * nj]); v.extend_from_slice(&s0.w[t * nk..(t + 1) * nk]); reps.push(v); }
            }
            // the machinery's own check: the full set of representatives must expand to an exact scheme
            if reps.len() * q == s0.r {
                let full = Sym::new(s0.g, q, [mat("MA"), mat("MB"), mat("MC")], reps.len(), &[]);
                let f0 = fmax_of(&full.expand(&reps.concat()), &t);
                println!("# the loaded scheme as {} orbits of {q}: max |F| {f0:.1e}", reps.len());
                assert!(f0 < 1e-9, "the loaded scheme does not have this symmetry");
            }
        }
        let found = std::sync::atomic::AtomicUsize::new(0);
        let done = std::sync::atomic::AtomicUsize::new(0);
        let mut res: Vec<f64> = pool.install(|| (0..runs).into_par_iter().map(|k| {
            let mut rng = Rng(seed.wrapping_mul(1_000_003).wrapping_add(k as u64));
            let mut x0: Vec<f64> = (0..sy.nred).map(|_| sigma * rng.normal()).collect();
            if let Some(drop) = symwarm {
                let mut gone = vec![false; reps.len()];
                if drop > 0 { gone[k % reps.len()] = true; }
                let mut left = drop.saturating_sub(1);
                while left > 0 { let c = (rng.next() % reps.len() as u64) as usize; if !gone[c] { gone[c] = true; left -= 1; } }
                let kept: Vec<&Vec<f64>> = reps.iter().zip(&gone).filter(|(_, g)| !**g).map(|(r, _)| r).collect();
                assert!(kept.len() >= m, "--orbits exceeds the orbits left");
                let per = kept[0].len();
                let rms = (kept.iter().map(|r| sq(r)).sum::<f64>() / (kept.len() * per) as f64).sqrt();
                for (o, r) in kept.iter().take(m).enumerate() { for (i, v) in r.iter().enumerate() { x0[o * per + i] = v + noise * rms * rng.normal(); } }
                // a fixed slot takes a known fixed product that lies in its eigenspaces (rotating with the run), if there is one
                for fi in 0..sy.f {
                    let fits: Vec<&[Vec<f64>; 3]> = known_fixed.iter().filter(|kf| (0..3).all(|s| {
                        let proj: f64 = sy.fixb[fi][s].iter().map(|b| dot(b, &kf[s]).powi(2)).sum();
                        (proj - sq(&kf[s])).abs() < 1e-8 * sq(&kf[s]) })).collect();
                    if fits.is_empty() { continue; }
                    let kf = fits[(k / reps.len().max(1) + k + fi) % fits.len()];
                    let mut off = sy.foff[fi];
                    for s in 0..3 { for b in &sy.fixb[fi][s] { x0[off] = dot(b, &kf[s]) + noise * rms * rng.normal(); off += 1; } }
                }
            }
            let (mut s, fm, nm, it) = lm_sym(&sy, x0, &t, iters, mu0, nmax, window, cnorm * target as f64);
            let ok = fm < 1e-10 && nm <= nmax;
            let dn = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
            if ok {
                let c = found.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                println!("start {k}: EXACT at rank {target}: |F| {fm:.1e}, largest product norm^2 {nm:.1}, {it} iterations ({:.0} s; {c} found of {dn} finished)", t0.elapsed().as_secs_f64());
                if let Some(dir) = &out {
                    std::fs::create_dir_all(dir).ok();
                    s.balance();
                    save(&s, fm, &format!("{dir}/{}x{}x{}_r{}_sym{q}_seed{seed}_start{k}.json", s.g[0], s.g[1], s.g[2], s.r));
                }
            } else if !o.quiet {
                println!("start {k}: |F| {fm:.2e}, norm^2 {nm:.1}, {it} iterations ({:.0} s)", t0.elapsed().as_secs_f64());
            }
            if ok { 0.0 } else { fm }
        }).collect());
        let nf = res.iter().filter(|x| **x == 0.0).count();
        res.retain(|x| *x > 0.0);
        res.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let qt = |p: f64| if res.is_empty() { 0.0 } else { res[((res.len() - 1) as f64 * p) as usize] };
        println!("# summary: rank {target} ({m} orbits of {q} + {f} fixed): {nf} of {runs} starts EXACT; the others' max |F|: min {:.2e}, median {:.2e}, max {:.2e}; {:.0} s",
                 qt(0.0), qt(0.5), qt(1.0), t0.elapsed().as_secs_f64());
        return;
    }
    if search > 0 || warm > 0 {
        // the numerical search: random starts at rank --search, or the scheme less --warm products plus noise
        let (iters, mu0, sigma, noise, nmax) = (opt("--iters", 2000.0) as usize, opt("--mu", 1e-2), opt("--init", 0.5), opt("--noise", 0.1), opt("--nmax", 1e4));
        let window = opt("--window", 25.0) as usize;
        let sparse = a.iter().any(|x| x == "--sparse");
        let clamp = opt("--clamp", 0.05);
        let rational = std::sync::atomic::AtomicUsize::new(0);
        let target = if warm > 0 { s0.r - warm } else { search };
        println!("# {name}: <{}x{}x{}> rank {target}, {runs} {} from seed {seed}, at most {iters} iterations, mu {mu0}, window {window}, {threads} threads",
                 s0.g[0], s0.g[1], s0.g[2], if warm > 0 { format!("warm starts (the rank-{} scheme less {warm}, noise {noise})", s0.r) } else { format!("random starts (sigma {sigma})") });
        let done = std::sync::atomic::AtomicUsize::new(0);
        let found = std::sync::atomic::AtomicUsize::new(0);
        let mut res: Vec<(f64, f64)> = pool.install(|| (0..runs).into_par_iter().map(|k| {
            let mut rng = Rng(seed.wrapping_mul(1_000_003).wrapping_add(k as u64));
            let mut s = if warm > 0 { warm_scheme(&s0, warm, noise, k, &mut rng) } else { random_scheme(s0.g, target, sigma, &mut rng) };
            let (mut f, nm, it, mu) = lm_search(&mut s, &t, iters, mu0, nmax, window);
            let mut note = String::new();
            if sparse && f < 1e-10 && nm <= nmax {       // clamp the scheme found to a sparse one, and try to read it as rational
                let (z, rd) = sparsify(&mut s, &t, 400, clamp);
                let mut den = rationalize(&mut s, &t);
                if den.is_none() { discretize(&mut s, &t); den = rationalize(&mut s, &t); }
                f = fmax_of(&s, &t);
                if den.is_some() { rational.fetch_add(1, std::sync::atomic::Ordering::Relaxed); }
                note = format!(", clamped: {:.0}% of the entries zero in {rd} rounds, {}", 100.0 * z as f64 / s.n() as f64,
                               match den { Some(d) => format!("EXACT OVER Q (entries in Z/{d}, verified in integers)"), None => "entries not simple".to_string() });
            }
            let ok = f < 1e-10 && nm <= nmax;
            let d = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
            if ok {
                let c = found.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
                println!("start {k}: EXACT at rank {target}: |F| {f:.1e}, largest product norm^2 {nm:.1}, {it} iterations{note} ({:.0} s; {c} found of {d} finished)", t0.elapsed().as_secs_f64());
                if let Some(dir) = &out {
                    std::fs::create_dir_all(dir).ok();
                    s.balance();
                    save(&s, f, &format!("{dir}/{}x{}x{}_r{}_lm_seed{seed}_start{k}.json", s.g[0], s.g[1], s.g[2], s.r));
                }
            } else if !o.quiet {
                println!("start {k}: |F| {f:.2e}, norm^2 {nm:.1}, {it} iterations, mu {mu:.0e} ({:.0} s)", t0.elapsed().as_secs_f64());
            }
            (if ok { 0.0 } else { f }, nm)
        }).collect());
        let nf = res.iter().filter(|x| x.0 == 0.0).count();
        res.retain(|x| x.0 > 0.0);
        res.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());
        let q = |p: f64| if res.is_empty() { 0.0 } else { res[((res.len() - 1) as f64 * p) as usize].0 };
        println!("# summary: rank {target}: {nf} of {runs} starts EXACT{}; the others' max |F|: min {:.2e}, median {:.2e}, max {:.2e}; {:.0} s",
                 if sparse { format!(" ({} of them exact over Q after clamping)", rational.load(std::sync::atomic::Ordering::Relaxed)) } else { String::new() },
                 q(0.0), q(0.5), q(1.0), t0.elapsed().as_secs_f64());
        return;
    }
    println!("# {name}: <{}x{}x{}:{}>, {runs} runs from seed {seed}, {} steps, kick {}, bound {}, {threads} threads", s0.g[0], s0.g[1], s0.g[2], s0.r, o.steps, o.kick, o.bound);
    let results: Vec<(usize, usize, f64)> = pool.install(|| (0..runs).into_par_iter().map(|k| {
        let tag = format!("[run {k}]");
        let (s, f) = run(&s0, &t, seed.wrapping_mul(1000).wrapping_add(k as u64), &o, &tag);
        let ok = f < 1e-10;
        println!("run {k}: {} -> {} products, |F| {:.1e} {}  ({:.0} s){}", s0.r, s.r, f, if ok { "EXACT" } else { "not a scheme" }, t0.elapsed().as_secs_f64(),
                 if ok && s.r < s0.r { "   <== BELOW THE START" } else { "" });
        if ok && s.r < s0.r { if let Some(dir) = &out {
            std::fs::create_dir_all(dir).ok();
            save(&s, f, &format!("{dir}/{}x{}x{}_r{}_seed{seed}_run{k}.json", s.g[0], s.g[1], s.g[2], s.r));
        } }
        (k, s.r, f)
    }).collect());
    let mut hist = std::collections::BTreeMap::new();
    for (_, r, f) in &results { *hist.entry((*r, *f < 1e-10)).or_insert(0) += 1; }
    println!("# summary: {}", hist.iter().map(|((r, ok), c)| format!("{r} products {}: {c}", if *ok { "exact" } else { "inexact" })).collect::<Vec<_>>().join(", "));
}
