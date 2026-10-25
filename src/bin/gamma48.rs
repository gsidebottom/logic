//! The (inf,2)-growth factor of Dumas, Pernet and Sedoglavic (arXiv:2603.18699, eq. 4) minimized
//! over the De Groot orbit of a <4x4x4:r> scheme: (U, V, W) in GL(4)^3 act on the row-major
//! matrices of the rows of L and R and of the columns of P as
//!
//!   Mat(L'_i) = U^-T Mat(L_i) V^T,   Mat(R'_i) = V^-T Mat(R_i) W^T,   Z'_i = U Z_i W^-1,
//!
//! and gamma_{inf,2} = max_pq sum_i ||Mat(L'_i)||_F ||Mat(R'_i)||_F |Z'_i[p,q]|.  The max and the
//! absolute value are smoothed (log-sum-exp with sharpness beta, sqrt(x^2 + eps^2)), minimized by
//! BFGS with the exact gradient (adjoint, below) along a continuation in (beta, eps); many random
//! starts on all cores.  A port of matmul/dps48/gamma/search_gl.py, about 100x faster.
//!
//!   gamma48 PREFIX ROLE STARTS [SEED] [--out FILE]     PREFIX_{L,R,P}.sms; ROLE 0-2 picks which
//!                                                      factor set computes the outputs
//!   gamma48 PREFIX ROLE --check-grad                   the gradient against central differences

use rayon::prelude::*;
use std::time::Instant;

type M4 = [[f64; 4]; 4];

const Z4: M4 = [[0.0; 4]; 4];

fn eye() -> M4 {
    let mut m = Z4;
    for (i, row) in m.iter_mut().enumerate() {
        row[i] = 1.0;
    }
    m
}

fn mul(a: &M4, b: &M4) -> M4 {
    let mut c = Z4;
    for i in 0..4 {
        for k in 0..4 {
            let x = a[i][k];
            for j in 0..4 {
                c[i][j] += x * b[k][j];
            }
        }
    }
    c
}

fn tr(a: &M4) -> M4 {
    let mut t = Z4;
    for i in 0..4 {
        for j in 0..4 {
            t[i][j] = a[j][i];
        }
    }
    t
}

fn add_scaled(acc: &mut M4, a: &M4, s: f64) {
    for i in 0..4 {
        for j in 0..4 {
            acc[i][j] += s * a[i][j];
        }
    }
}

fn frob(a: &M4) -> f64 {
    a.iter().flatten().map(|x| x * x).sum::<f64>().sqrt()
}

/// inverse by cofactors (no branches); None when (nearly) singular
fn inv(m: &M4) -> Option<M4> {
    let a = |i: usize, j: usize| m[i][j];
    let s0 = a(0, 0) * a(1, 1) - a(1, 0) * a(0, 1);
    let s1 = a(0, 0) * a(1, 2) - a(1, 0) * a(0, 2);
    let s2 = a(0, 0) * a(1, 3) - a(1, 0) * a(0, 3);
    let s3 = a(0, 1) * a(1, 2) - a(1, 1) * a(0, 2);
    let s4 = a(0, 1) * a(1, 3) - a(1, 1) * a(0, 3);
    let s5 = a(0, 2) * a(1, 3) - a(1, 2) * a(0, 3);
    let c5 = a(2, 2) * a(3, 3) - a(3, 2) * a(2, 3);
    let c4 = a(2, 1) * a(3, 3) - a(3, 1) * a(2, 3);
    let c3 = a(2, 1) * a(3, 2) - a(3, 1) * a(2, 2);
    let c2 = a(2, 0) * a(3, 3) - a(3, 0) * a(2, 3);
    let c1 = a(2, 0) * a(3, 2) - a(3, 0) * a(2, 2);
    let c0 = a(2, 0) * a(3, 1) - a(3, 0) * a(2, 1);
    let det = s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0;
    let scale = m.iter().flatten().map(|x| x.abs()).fold(0.0, f64::max).max(1e-300);
    if !det.is_finite() || det.abs() < 1e-12 * scale.powi(4) {
        return None;
    }
    let d = 1.0 / det;
    Some([
        [
            (a(1, 1) * c5 - a(1, 2) * c4 + a(1, 3) * c3) * d,
            (-a(0, 1) * c5 + a(0, 2) * c4 - a(0, 3) * c3) * d,
            (a(3, 1) * s5 - a(3, 2) * s4 + a(3, 3) * s3) * d,
            (-a(2, 1) * s5 + a(2, 2) * s4 - a(2, 3) * s3) * d,
        ],
        [
            (-a(1, 0) * c5 + a(1, 2) * c2 - a(1, 3) * c1) * d,
            (a(0, 0) * c5 - a(0, 2) * c2 + a(0, 3) * c1) * d,
            (-a(3, 0) * s5 + a(3, 2) * s2 - a(3, 3) * s1) * d,
            (a(2, 0) * s5 - a(2, 2) * s2 + a(2, 3) * s1) * d,
        ],
        [
            (a(1, 0) * c4 - a(1, 1) * c2 + a(1, 3) * c0) * d,
            (-a(0, 0) * c4 + a(0, 1) * c2 - a(0, 3) * c0) * d,
            (a(3, 0) * s4 - a(3, 1) * s2 + a(3, 3) * s0) * d,
            (-a(2, 0) * s4 + a(2, 1) * s2 - a(2, 3) * s0) * d,
        ],
        [
            (-a(1, 0) * c3 + a(1, 1) * c1 - a(1, 2) * c0) * d,
            (a(0, 0) * c3 - a(0, 1) * c1 + a(0, 2) * c0) * d,
            (-a(3, 0) * s3 + a(3, 1) * s1 - a(3, 2) * s0) * d,
            (a(2, 0) * s3 - a(2, 1) * s1 + a(2, 2) * s0) * d,
        ],
    ])
}

fn det(m: &M4) -> f64 {
    // by elimination with partial pivoting (only for normalizing)
    let mut a = *m;
    let mut d = 1.0;
    for c in 0..4 {
        let p = (c..4).max_by(|&i, &j| a[i][c].abs().total_cmp(&a[j][c].abs())).unwrap();
        if a[p][c] == 0.0 {
            return 0.0;
        }
        if p != c {
            a.swap(p, c);
            d = -d;
        }
        d *= a[c][c];
        for r in c + 1..4 {
            let f = a[r][c] / a[c][c];
            for k in c..4 {
                a[r][k] -= f * a[c][k];
            }
        }
    }
    d
}

/// a scheme: the row-major 4x4 matrices of the rows of L (A_i) and R (B_i) and of the columns
/// of P (Z_i)
#[derive(Clone)]
struct Scheme {
    a: Vec<M4>,
    b: Vec<M4>,
    z: Vec<M4>,
}

fn read_sms(path: &str) -> Vec<Vec<f64>> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut lines = text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#'));
    let head: Vec<usize> = lines.next().unwrap().split_whitespace().take(2).map(|x| x.parse().unwrap()).collect();
    let mut m = vec![vec![0.0; head[1]]; head[0]];
    for l in lines {
        let f: Vec<&str> = l.split_whitespace().collect();
        let (i, j): (usize, usize) = (f[0].parse().unwrap(), f[1].parse().unwrap());
        if i == 0 {
            break;
        }
        let v = match f[2].split_once('/') {
            Some((p, q)) => p.parse::<f64>().unwrap() / q.parse::<f64>().unwrap(),
            None => f[2].parse().unwrap(),
        };
        m[i - 1][j - 1] = v;
    }
    m
}

fn mat_of(v: impl Fn(usize) -> f64) -> M4 {
    let mut m = Z4;
    for p in 0..4 {
        for q in 0..4 {
            m[p][q] = v(4 * p + q);
        }
    }
    m
}

impl Scheme {
    fn load(prefix: &str) -> Scheme {
        let l = read_sms(&format!("{prefix}_L.sms"));
        let r = read_sms(&format!("{prefix}_R.sms"));
        let p = read_sms(&format!("{prefix}_P.sms"));
        let n = l.len();
        assert!(r.len() == n && p[0].len() == n && l[0].len() == 16 && r[0].len() == 16 && p.len() == 16);
        Scheme {
            a: (0..n).map(|i| mat_of(|k| l[i][k])).collect(),
            b: (0..n).map(|i| mat_of(|k| r[i][k])).collect(),
            z: (0..n).map(|i| mat_of(|k| p[k][i])).collect(),
        }
    }

    /// rotation k of the trace-form triple (X_i, Y_i, Z_i) = (A_i^T, B_i^T, Z_i): factor set k
    /// computes the outputs
    fn role(&self, k: usize) -> Scheme {
        let x: Vec<M4> = self.a.iter().map(tr).collect();
        let y: Vec<M4> = self.b.iter().map(tr).collect();
        let z = self.z.clone();
        let (x, y, z) = match k {
            0 => (x, y, z),
            1 => (y, z, x),
            _ => (z, x, y),
        };
        Scheme { a: x.iter().map(tr).collect(), b: y.iter().map(tr).collect(), z }
    }

    /// the scheme transformed by (U, V, W)
    fn act(&self, u: &M4, v: &M4, w: &M4) -> Option<Scheme> {
        let (iut, ivt, iw) = (tr(&inv(u)?), tr(&inv(v)?), inv(w)?);
        let (vt, wt) = (tr(v), tr(w));
        Some(Scheme {
            a: self.a.iter().map(|m| mul(&mul(&iut, m), &vt)).collect(),
            b: self.b.iter().map(|m| mul(&mul(&ivt, m), &wt)).collect(),
            z: self.z.iter().map(|m| mul(&mul(u, m), &iw)).collect(),
        })
    }

    fn g_inf2(&self) -> f64 {
        let mut v = Z4;
        for i in 0..self.a.len() {
            add_scaled(&mut v, &self.z[i].map(|r| r.map(f64::abs)), frob(&self.a[i]) * frob(&self.b[i]));
        }
        v.iter().flatten().cloned().fold(0.0, f64::max)
    }

    fn g_inf_inf(&self) -> f64 {
        let n1 = |m: &M4| m.iter().flatten().map(|x| x.abs()).sum::<f64>();
        let mut v = Z4;
        for i in 0..self.a.len() {
            add_scaled(&mut v, &self.z[i].map(|r| r.map(f64::abs)), n1(&self.a[i]) * n1(&self.b[i]));
        }
        v.iter().flatten().cloned().fold(0.0, f64::max)
    }

    fn gamma2(&self) -> f64 {
        (0..self.a.len()).map(|i| frob(&self.a[i]) * frob(&self.b[i]) * frob(&self.z[i])).sum()
    }

    /// largest deviation from the matrix multiplication tensor: sum_i tr(X_i A) tr(Y_i B) tr(Z_i G)
    /// = tr(A B G) for every basis triple
    fn brent_error(&self) -> f64 {
        let mut worst: f64 = 0.0;
        for a in 0..16 {
            for b in 0..16 {
                for c in 0..16 {
                    let (ai, aj, bi, bj, ci, cj) = (a / 4, a % 4, b / 4, b % 4, c / 4, c % 4);
                    let t: f64 = (0..self.a.len()).map(|i| self.a[i][ai][aj] * self.b[i][bi][bj] * self.z[i][ci][cj]).sum();
                    let want = if aj == bi && ai == ci && bj == cj { 1.0 } else { 0.0 };
                    worst = worst.max((t - want).abs());
                }
            }
        }
        worst
    }
}

/// the point: U, V, W
#[derive(Clone, Copy)]
struct Point([M4; 3]);

impl Point {
    fn from_vec(x: &[f64]) -> Point {
        let mut p = [Z4; 3];
        for (k, m) in p.iter_mut().enumerate() {
            *m = mat_of(|t| x[16 * k + t]);
        }
        Point(p)
    }
    fn to_vec(&self) -> Vec<f64> {
        self.0.iter().flat_map(|m| m.iter().flatten().cloned()).collect()
    }
    /// each of U, V, W scaled to |det| 1 (gamma does not change)
    fn normalized(&self) -> Point {
        Point(self.0.map(|m| {
            let d = det(&m).abs();
            if d > 0.0 { m.map(|r| r.map(|x| x / d.powf(0.25))) } else { m }
        }))
    }
}

/// the smoothed objective and its gradient (by the adjoint): f = (1/beta) log sum_pq exp(beta
/// v_pq), v_pq = sum_i a_i b_i s(Z'_i[p,q]), s(x) = sqrt(x^2 + eps^2); None off GL(4)^3
fn objective(s: &Scheme, x: &[f64], beta: f64, eps: f64, grad: Option<&mut [f64]>) -> Option<f64> {
    let Point([u, v, w]) = Point::from_vec(x);
    let (iu, iv, iw) = (inv(&u)?, inv(&v)?, inv(&w)?);
    let (iut, ivt, vt, wt) = (tr(&iu), tr(&iv), tr(&v), tr(&w));
    let n = s.a.len();
    let mut ma = Vec::with_capacity(n);
    let mut mb = Vec::with_capacity(n);
    let mut zp = Vec::with_capacity(n);
    let mut ab = vec![0.0; n];
    let mut vals = Z4;
    for i in 0..n {
        let a = mul(&mul(&iut, &s.a[i]), &vt);
        let b = mul(&mul(&ivt, &s.b[i]), &wt);
        let z = mul(&mul(&u, &s.z[i]), &iw);
        ab[i] = frob(&a) * frob(&b);
        for p in 0..4 {
            for q in 0..4 {
                vals[p][q] += ab[i] * (z[p][q] * z[p][q] + eps * eps).sqrt();
            }
        }
        ma.push(a);
        mb.push(b);
        zp.push(z);
    }
    let vmax = vals.iter().flatten().cloned().fold(f64::MIN, f64::max);
    let mut pi = vals.map(|r| r.map(|t| (beta * (t - vmax)).exp()));
    let sum: f64 = pi.iter().flatten().sum();
    let f = vmax + sum.ln() / beta;
    if !f.is_finite() {
        return None;
    }
    let Some(g) = grad else { return Some(f) };
    pi = pi.map(|r| r.map(|t| t / sum));
    // adjoints of U, V, W and of their inverses
    let (mut gu, mut gv, mut gw, mut giu, mut giv, mut giw) = (Z4, Z4, Z4, Z4, Z4, Z4);
    for i in 0..n {
        let (a, b) = (frob(&ma[i]), frob(&mb[i]));
        let mut gz = Z4;
        let mut si = 0.0;
        for p in 0..4 {
            for q in 0..4 {
                let t = zp[i][p][q];
                let sv = (t * t + eps * eps).sqrt();
                si += pi[p][q] * sv;
                gz[p][q] = pi[p][q] * ab[i] * t / sv;
            }
        }
        // df/dMA_i = b S_i MA_i / a, df/dMB_i = a S_i MB_i / b
        let ga = ma[i].map(|r| r.map(|t| b * si * t / a));
        let gb = mb[i].map(|r| r.map(|t| a * si * t / b));
        // MA = iU^T A V^T: d/d iU = A V^T GA^T, d/dV = GA^T iU^T A
        add_scaled(&mut giu, &mul(&mul(&s.a[i], &vt), &tr(&ga)), 1.0);
        add_scaled(&mut gv, &mul(&mul(&tr(&ga), &iut), &s.a[i]), 1.0);
        // MB = iV^T B W^T: d/d iV = B W^T GB^T, d/dW = GB^T iV^T B
        add_scaled(&mut giv, &mul(&mul(&s.b[i], &wt), &tr(&gb)), 1.0);
        add_scaled(&mut gw, &mul(&mul(&tr(&gb), &ivt), &s.b[i]), 1.0);
        // Z' = U Z iW: d/dU = GZ iW^T Z^T, d/d iW = Z^T U^T GZ
        add_scaled(&mut gu, &mul(&mul(&gz, &tr(&iw)), &tr(&s.z[i])), 1.0);
        add_scaled(&mut giw, &mul(&mul(&tr(&s.z[i]), &tr(&u)), &gz), 1.0);
    }
    // through the inverses: X = M^-1, df/dM = -X^T (df/dX) X^T
    add_scaled(&mut gu, &mul(&mul(&iut, &giu), &iut), -1.0);
    add_scaled(&mut gv, &mul(&mul(&ivt, &giv), &ivt), -1.0);
    add_scaled(&mut gw, &mul(&mul(&tr(&iw), &giw), &tr(&iw)), -1.0);
    for (k, m) in [gu, gv, gw].iter().enumerate() {
        for p in 0..4 {
            for q in 0..4 {
                g[16 * k + 4 * p + q] = m[p][q];
            }
        }
    }
    Some(f)
}

/// the true gamma_{inf,2} at x
fn true_gamma(s: &Scheme, x: &[f64]) -> f64 {
    let Point([u, v, w]) = Point::from_vec(x);
    s.act(&u, &v, &w).map_or(f64::INFINITY, |t| t.g_inf2())
}

/// BFGS (dense inverse Hessian) with a backtracking Armijo line search
fn bfgs(s: &Scheme, x0: &[f64], beta: f64, eps: f64, iters: usize) -> Vec<f64> {
    let n = x0.len();
    let mut x = x0.to_vec();
    let mut g = vec![0.0; n];
    let Some(mut f) = objective(s, &x, beta, eps, Some(&mut g)) else { return x };
    let mut h = vec![0.0; n * n];
    for i in 0..n {
        h[i * n + i] = 1.0;
    }
    let mut gn = vec![0.0; n];
    for _ in 0..iters {
        let d: Vec<f64> = (0..n).map(|i| -(0..n).map(|j| h[i * n + j] * g[j]).sum::<f64>()).collect();
        let slope: f64 = (0..n).map(|i| d[i] * g[i]).sum();
        let (d, slope) = if slope < 0.0 { (d, slope) } else {
            // not a descent direction: reset to steepest descent
            h.iter_mut().enumerate().for_each(|(k, e)| *e = if k % (n + 1) == 0 { 1.0 } else { 0.0 });
            let d: Vec<f64> = g.iter().map(|t| -t).collect();
            let sl = -g.iter().map(|t| t * t).sum::<f64>();
            (d, sl)
        };
        let mut step = 1.0;
        let mut accepted = None;
        for _ in 0..60 {
            let xn: Vec<f64> = (0..n).map(|i| x[i] + step * d[i]).collect();
            if let Some(fnew) = objective(s, &xn, beta, eps, Some(&mut gn)) {
                if fnew <= f + 1e-4 * step * slope {
                    accepted = Some((xn, fnew));
                    break;
                }
            }
            step *= 0.5;
        }
        let Some((xn, fnew)) = accepted else { break };
        let sv: Vec<f64> = (0..n).map(|i| xn[i] - x[i]).collect();
        let yv: Vec<f64> = (0..n).map(|i| gn[i] - g[i]).collect();
        let sy: f64 = (0..n).map(|i| sv[i] * yv[i]).sum();
        let df = f - fnew;
        x = xn;
        f = fnew;
        g.copy_from_slice(&gn);
        if sy > 1e-14 {
            // H <- (I - rho s y^T) H (I - rho y s^T) + rho s s^T
            let rho = 1.0 / sy;
            let hy: Vec<f64> = (0..n).map(|i| (0..n).map(|j| h[i * n + j] * yv[j]).sum()).collect();
            let yhy: f64 = (0..n).map(|i| yv[i] * hy[i]).sum();
            for i in 0..n {
                for j in 0..n {
                    h[i * n + j] += -rho * (hy[i] * sv[j] + sv[i] * hy[j]) + (rho * rho * yhy + rho) * sv[i] * sv[j];
                }
            }
        }
        let gmax = g.iter().map(|t| t.abs()).fold(0.0, f64::max);
        if gmax < 1e-10 || df.abs() < 1e-15 * f.abs().max(1.0) {
            break;
        }
    }
    x
}

/// a small random generator (splitmix64) with normal deviates
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn unit(&mut self) -> f64 {
        ((self.next() >> 11) as f64 + 0.5) / 9007199254740992.0
    }
    fn normal(&mut self) -> f64 {
        (-2.0 * self.unit().ln()).sqrt() * (2.0 * std::f64::consts::PI * self.unit()).cos()
    }
}

/// a random rotation (Cayley transform of a random skew matrix) times I + noise
fn random_matrix(rng: &mut Rng, rot: f64, noise: f64) -> M4 {
    let mut sk = Z4;
    for p in 0..4 {
        for q in p + 1..4 {
            let t = rot * rng.normal();
            sk[p][q] = t;
            sk[q][p] = -t;
        }
    }
    let i = eye();
    let mut ip = i;
    let mut im = i;
    add_scaled(&mut ip, &sk, 1.0);
    add_scaled(&mut im, &sk, -1.0);
    let q = mul(&im, &inv(&ip).unwrap_or(i));
    let mut e = i;
    for row in e.iter_mut() {
        for t in row.iter_mut() {
            *t += noise * rng.normal();
        }
    }
    mul(&q, &e)
}

/// one start: the continuation from a random point (seed 0: the scheme itself)
fn start(s: &Scheme, seed: u64) -> (f64, u64, Vec<f64>) {
    let mut rng = Rng(seed.wrapping_mul(0x2545f4914f6cdd1d) ^ 0x5851f42d4c957f2d);
    let kind = seed % 4;
    let x0: Vec<f64> = if seed == 0 {
        Point([eye(); 3]).to_vec()
    } else {
        let (rot, noise) = match kind {
            0 | 1 => (0.0, 0.15),
            2 => (1.0, [0.3, 0.6, 1.0][(seed / 4 % 3) as usize]),
            _ => (1.0, 0.0),
        };
        Point([0, 1, 2].map(|_| random_matrix(&mut rng, rot, noise))).to_vec()
    };
    let mut x = x0;
    for (beta, eps) in [(0.5, 1e-1), (2.0, 3e-2), (8.0, 1e-2), (32.0, 3e-3), (128.0, 1e-3), (512.0, 3e-4), (2048.0, 1e-4),
                        (8192.0, 1e-5), (32768.0, 1e-6)] {
        x = Point::from_vec(&bfgs(s, &x, beta, eps, 3000)).normalized().to_vec();
    }
    (true_gamma(s, &x), seed, x)
}

fn show(m: &M4) -> String {
    m.iter().map(|r| r.iter().map(|t| format!("{:9.5}", if t.abs() < 5e-6 { 0.0 } else { *t })).collect::<Vec<_>>().join(" "))
        .collect::<Vec<_>>().join(" | ")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        eprintln!("usage: gamma48 PREFIX ROLE STARTS [SEED] [--out FILE] | gamma48 PREFIX ROLE --check-grad");
        std::process::exit(2);
    }
    let base = Scheme::load(&args[1]);
    let role: usize = args[2].parse().unwrap();
    let s = base.role(role);
    assert!(s.brent_error() < 1e-12, "the role-rotated scheme is not a matrix multiplication");
    if args[3] == "--check-grad" {
        let mut rng = Rng(7);
        for t in 0..5 {
            let x = Point([0, 1, 2].map(|_| random_matrix(&mut rng, 1.0, 0.3))).to_vec();
            let (beta, eps) = [(0.5, 0.1), (8.0, 1e-2), (128.0, 1e-3), (1.0, 0.05), (32.0, 3e-3)][t];
            let mut g = vec![0.0; 48];
            objective(&s, &x, beta, eps, Some(&mut g)).unwrap();
            let mut worst: f64 = 0.0;
            for k in 0..48 {
                let h = 1e-6;
                let (mut xp, mut xm) = (x.clone(), x.clone());
                xp[k] += h;
                xm[k] -= h;
                let fd = (objective(&s, &xp, beta, eps, None).unwrap() - objective(&s, &xm, beta, eps, None).unwrap()) / (2.0 * h);
                worst = worst.max((fd - g[k]).abs() / g.iter().map(|t| t.abs()).fold(1e-12, f64::max));
            }
            println!("beta {beta:7.1} eps {eps:.0e}: largest gradient difference {worst:.2e} (relative to the largest component)");
        }
        return;
    }
    let starts: u64 = args[3].parse().unwrap();
    let seed0: u64 = args.get(4).filter(|a| !a.starts_with("--")).map_or(0, |a| a.parse().unwrap());
    let out = args.iter().position(|a| a == "--out").map(|i| args[i + 1].clone());
    println!("# gamma48 {} role {role}: start g(inf,2) {:.4}, gamma2 {:.4}, g(inf,inf) {:.2}; {starts} starts from seed {seed0} on {} threads",
             args[1], s.g_inf2(), s.gamma2(), s.g_inf_inf(), rayon::current_num_threads());
    let t = Instant::now();
    let mut res: Vec<(f64, u64, Vec<f64>)> = (seed0..seed0 + starts).into_par_iter().map(|sd| start(&s, sd)).collect();
    res.sort_by(|a, b| a.0.total_cmp(&b.0));
    println!("# {starts} starts in {:.1} s", t.elapsed().as_secs_f64());
    // the distinct local optima found (to 1e-4), with how often
    let mut levels: Vec<(f64, usize)> = vec![];
    for (g, _, _) in &res {
        match levels.last_mut() {
            Some((v, c)) if (g - *v).abs() < 1e-4 * v.abs() => *c += 1,
            _ => levels.push((*g, 1)),
        }
    }
    println!("# local optima (value x count): {}",
             levels.iter().take(12).map(|(v, c)| format!("{v:.4} x{c}")).collect::<Vec<_>>().join("  "));
    let (g, sd, x) = &res[0];
    let Point([u, v, w]) = Point::from_vec(x);
    let t2 = s.act(&u, &v, &w).unwrap();
    println!("# best: seed {sd}  g(inf,2) {g:.6}  gamma2 {:.4}  g(inf,inf) {:.3}  brent err {:.1e}", t2.gamma2(), t2.g_inf_inf(),
             t2.brent_error());
    println!("# U = {}\n# V = {}\n# W = {}", show(&u), show(&v), show(&w));
    if let Some(path) = out {
        let text = res.iter().take(50).map(|(g, sd, x)| {
            format!("{g:.10} {sd} {}", x.iter().map(|t| format!("{t:.15e}")).collect::<Vec<_>>().join(" "))
        }).collect::<Vec<_>>().join("\n");
        std::fs::write(&path, text + "\n").unwrap();
        println!("# the best 50 points (gamma, seed, U V W row-major) in {path}");
    }
}
