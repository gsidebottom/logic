//! kronexact: exact replay over Q of a kronkill path, and an exact check of every Brent equation.
//!
//! kronkill (src/bin/kronkill.rs) searches projections and 2-reductions of a matrix multiplication scheme
//! modulo one 20-bit prime and writes a path file: per stage the deleted index, per reduction step the
//! direction, the pivot products and the support of the dependencies.  This program redoes the path over the
//! rationals and certifies the result.
//!
//! Prior art: 2-reducibility is LITA's (Khoruzhii, Serafin, Gelss, Pokutta, github.com/khoruzhii/lita).
//!
//! replay: for every step, the dependencies of the Kronecker products K_t (t in the support) are the null space
//!   of their Gram matrix (X_r X_r^T) o (X_c X_c^T).  It is computed modulo three primes just below 2^61 with
//!   the pivots as the free columns, lifted to Q from the first two (Chinese remainder + rational
//!   reconstruction) and compared with the third.  The fold f_s -= sum_j N[j][s] f_{J_j} is done in exact
//!   rational arithmetic (64-bit numerators and denominators, every overflow is a panic).
//! check: with D_u, D_v, D_w the common denominators of the three factors, every one of the
//!   (n0 n1)(n1 n2)(n2 n0) Brent equations sum_t U_t[a] V_t[b] W_t[c] = D_u D_v D_w [target] is evaluated in
//!   128-bit integers, after a proof that no partial sum can overflow.  A copy with one changed coefficient
//!   must fail.  THE CHECK IS THE CERTIFICATE: it does not depend on how the scheme was found, so nothing in
//!   the replay has to be trusted.
//!
//! usage: kronexact check SCHEME.json[.gz]
//!        kronexact replay SOURCE.json[.gz] PATH.json OUT.json [--check-input] [--dense] [--catalog DIR]
//!        kronexact build PLAN.json OUT.json [--dense] [--catalog DIR]
//! build: executes a plan of constructions (file, schoolbook, rotation / transposition, sub-format, direct sum,
//!   Kronecker product, shared-factor product) and certifies the result with the same check.
//!   A file node of a plan names its scheme by "path" (as given), by "here" (relative to the plan's own
//!   directory) or by "catalog" (relative to the root of a scheme catalog, given with --catalog DIR).
//! replay with a SOURCE whose name ends in plan.json builds that plan first and replays the path on the result.
//! Layout as in the catalog: u on A (n0 x n1 row-major), v on B (n1 x n2), w on C^T (index k * n0 + i).

use rayon::prelude::*;
use serde_json::{Value, json};
use std::time::Instant;

const RC: [(usize, usize); 3] = [(1, 2), (0, 2), (0, 1)];

// ---------------------------------------------------------------- exact rationals, 64-bit

fn gcd(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a.abs()
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Q {
    n: i64,
    d: i64,
}

impl Q {
    const ZERO: Q = Q { n: 0, d: 1 };
    fn new(n: i128, d: i128) -> Q {
        assert!(d != 0, "zero denominator");
        let g = gcd(n, d).max(1);
        let (mut n, mut d) = (n / g, d / g);
        if d < 0 {
            (n, d) = (-n, -d);
        }
        Q { n: i64::try_from(n).expect("numerator beyond 64 bits"), d: i64::try_from(d).expect("denominator beyond 64 bits") }
    }
    fn mul(self, o: Q) -> Q {
        Q::new(self.n as i128 * o.n as i128, self.d as i128 * o.d as i128)
    }
    fn sub(self, o: Q) -> Q {
        Q::new(self.n as i128 * o.d as i128 - o.n as i128 * self.d as i128, self.d as i128 * o.d as i128)
    }
    fn add(self, o: Q) -> Q {
        Q::new(self.n as i128 * o.d as i128 + o.n as i128 * self.d as i128, self.d as i128 * o.d as i128)
    }
    fn div(self, o: Q) -> Q {
        assert!(o.n != 0, "division by zero");
        Q::new(self.n as i128 * o.d as i128, self.d as i128 * o.n as i128)
    }
    fn is_zero(self) -> bool {
        self.n == 0
    }
    fn show(self) -> Value {
        if self.d == 1 { json!(self.n) } else { json!(format!("{}/{}", self.n, self.d)) }
    }
}

/// "12", "-3/4", "0.25", "1.5/2": exact.
fn parse_q(s: &str) -> Q {
    fn dec(s: &str) -> (i128, i128) {
        let s = s.trim();
        let (neg, body) = match s.strip_prefix('-') {
            Some(r) => (true, r),
            None => (false, s.strip_prefix('+').unwrap_or(s)),
        };
        let (mut num, mut den, mut frac) = (0i128, 1i128, false);
        for ch in body.chars() {
            match ch {
                '0'..='9' => {
                    num = num.checked_mul(10).unwrap().checked_add(ch as i128 - '0' as i128).unwrap();
                    if frac {
                        den = den.checked_mul(10).unwrap();
                    }
                }
                '.' => frac = true,
                _ => panic!("cannot parse the entry {s:?}"),
            }
        }
        (if neg { -num } else { num }, den)
    }
    let mut parts = s.split('/');
    let (a, b) = dec(parts.next().unwrap());
    let (c, d) = parts.next().map(dec).unwrap_or((1, 1));
    assert!(parts.next().is_none(), "cannot parse the entry {s:?}");
    let g1 = gcd(a, b).max(1);
    let g2 = gcd(c, d).max(1);
    Q::new((a / g1).checked_mul(d / g2).unwrap(), (b / g1).checked_mul(c / g2).unwrap())
}

// ---------------------------------------------------------------- schemes over Q, sparse rows

#[derive(Clone)]
struct Scheme {
    n: [usize; 3],
    x: [Vec<Vec<(u32, Q)>>; 3], // per slot, per product: (column, value), columns increasing, values nonzero
}

fn cols_of(n: [usize; 3], s: usize) -> usize {
    match s {
        0 => n[0] * n[1],
        1 => n[1] * n[2],
        _ => n[2] * n[0],
    }
}

impl Scheme {
    fn m(&self) -> usize {
        self.x[0].len()
    }
    fn cols(&self, s: usize) -> usize {
        cols_of(self.n, s)
    }
}

fn entry(v: &Value) -> Q {
    match v {
        Value::Number(x) => parse_q(&x.to_string()),
        Value::String(x) => parse_q(x),
        _ => panic!("unexpected entry {v}"),
    }
}

fn load(path: &str) -> Scheme {
    let text = if path.ends_with(".gz") {
        // no compression crate: the system's gzip
        let o = std::process::Command::new("gzip").args(["-dc", path]).output().unwrap_or_else(|e| panic!("gzip -dc {path}: {e}"));
        assert!(o.status.success(), "gzip -dc {path} failed");
        String::from_utf8(o.stdout).expect("UTF-8")
    } else {
        std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"))
    };
    let d: Value = serde_json::from_str(&text).expect("JSON");
    drop(text);
    let n: Vec<usize> = d["n"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as usize).collect();
    let n = [n[0], n[1], n[2]];
    let m = d["m"].as_u64().unwrap() as usize;
    let mut x: [Vec<Vec<(u32, Q)>>; 3] = [vec![], vec![], vec![]];
    for (s, key) in ["u", "v", "w"].iter().enumerate() {
        let rows = d[*key].as_array().unwrap();
        assert_eq!(rows.len(), m, "{key} has {} rows, m = {m}", rows.len());
        let c = cols_of(n, s);
        for row in rows {
            let row = row.as_array().unwrap();
            let mut out: Vec<(u32, Q)> = Vec::new();
            if row.first().is_some_and(|e| e.is_object()) || row.is_empty() {
                for e in row {
                    let i = e["index"].as_u64().expect("sparse entry without an index") as usize;
                    assert!(i < c, "sparse index {i} out of range {c}");
                    let q = entry(&e["value"]);
                    if !q.is_zero() {
                        out.push((i as u32, q));
                    }
                }
                out.sort_by_key(|e| e.0);
                assert!(out.windows(2).all(|w| w[0].0 < w[1].0), "a sparse row repeats an index");
            } else {
                assert_eq!(row.len(), c);
                for (i, v) in row.iter().enumerate() {
                    let q = entry(v);
                    if !q.is_zero() {
                        out.push((i as u32, q));
                    }
                }
            }
            x[s].push(out);
        }
    }
    Scheme { n, x }
}

fn save(sc: &Scheme, path: &str, dense: bool, note: Value) {
    let mut d = serde_json::Map::new();
    d.insert("n".into(), json!(sc.n));
    d.insert("m".into(), json!(sc.m()));
    d.insert("z2".into(), json!(false));
    d.insert("note".into(), note);
    for (s, key) in ["u", "v", "w"].iter().enumerate() {
        let c = sc.cols(s);
        let rows: Vec<Value> = sc.x[s]
            .iter()
            .map(|row| {
                if dense {
                    let mut v = vec![json!(0); c];
                    for &(i, q) in row {
                        v[i as usize] = q.show();
                    }
                    Value::Array(v)
                } else {
                    Value::Array(row.iter().map(|&(i, q)| json!({"index": i, "value": q.show()})).collect())
                }
            })
            .collect();
        d.insert((*key).into(), Value::Array(rows));
    }
    std::fs::write(path, serde_json::to_string(&Value::Object(d)).unwrap()).unwrap();
}

/// Delete one index of slot `slot` (0 = I, 1 = J, 2 = K): kronkill's `project`, same order of the survivors.
fn project(sc: &Scheme, slot: usize, index: usize) -> Scheme {
    let n = sc.n;
    assert!(index < n[slot], "index {index} out of range for slot {slot} of {n:?}");
    let keep: Vec<Vec<usize>> = (0..3).map(|t| (0..n[t]).filter(|&j| !(t == slot && j == index)).collect()).collect();
    let (ki, kj, kk) = (&keep[0], &keep[1], &keep[2]);
    let cu: Vec<usize> = ki.iter().flat_map(|&i| kj.iter().map(move |&j| i * n[1] + j)).collect();
    let cv: Vec<usize> = kj.iter().flat_map(|&j| kk.iter().map(move |&k| j * n[2] + k)).collect();
    let cw: Vec<usize> = kk.iter().flat_map(|&k| ki.iter().map(move |&i| k * n[0] + i)).collect();
    let maps: Vec<Vec<u32>> = [cu, cv, cw]
        .iter()
        .enumerate()
        .map(|(s, cs)| {
            let mut mp = vec![u32::MAX; sc.cols(s)];
            for (new, &old) in cs.iter().enumerate() {
                mp[old] = new as u32;
            }
            mp
        })
        .collect();
    let mut n2 = n;
    n2[slot] -= 1;
    let mut x: [Vec<Vec<(u32, Q)>>; 3] = [vec![], vec![], vec![]];
    for t in 0..sc.m() {
        let rows: Vec<Vec<(u32, Q)>> = (0..3)
            .map(|s| {
                let mut r: Vec<(u32, Q)> = sc.x[s][t].iter().filter(|e| maps[s][e.0 as usize] != u32::MAX).map(|e| (maps[s][e.0 as usize], e.1)).collect();
                r.sort_by_key(|e| e.0);
                r
            })
            .collect();
        if rows.iter().all(|r| !r.is_empty()) {
            for (s, r) in rows.into_iter().enumerate() {
                x[s].push(r);
            }
        }
    }
    Scheme { n: n2, x }
}

// ---------------------------------------------------------------- arithmetic modulo q = 2^61 - c

#[derive(Clone, Copy)]
struct Fp {
    q: u64,
    c: u128,
}

const M61: u128 = (1u128 << 61) - 1;

impl Fp {
    #[inline]
    fn red(self, x: u128) -> u64 {
        let y = (x & M61) + (x >> 61) * self.c; // below 2^61 + 2^67 c
        let y = (y & M61) + (y >> 61) * self.c; // below 2^61 + 2^47
        let mut z = y as u64;
        while z >= self.q {
            z -= self.q;
        }
        z
    }
    #[inline]
    fn mul(self, a: u64, b: u64) -> u64 {
        self.red(a as u128 * b as u128)
    }
    fn pow(self, mut a: u64, mut e: u64) -> u64 {
        let mut r = 1u64;
        while e > 0 {
            if e & 1 == 1 {
                r = self.mul(r, a);
            }
            a = self.mul(a, a);
            e >>= 1;
        }
        r
    }
    fn inv(self, a: u64) -> u64 {
        assert!(a % self.q != 0, "inverse of zero modulo {}", self.q);
        self.pow(a % self.q, self.q - 2)
    }
    fn of_i64(self, a: i64) -> u64 {
        (a as i128).rem_euclid(self.q as i128) as u64
    }
    fn of_q(self, v: Q) -> u64 {
        let d = self.of_i64(v.d);
        assert!(d != 0, "a denominator is divisible by {}", self.q);
        self.mul(self.of_i64(v.n), self.inv(d))
    }
}

fn is_prime(n: u64) -> bool {
    fn mulmod(a: u64, b: u64, n: u64) -> u64 {
        (a as u128 * b as u128 % n as u128) as u64
    }
    fn powmod(mut a: u64, mut e: u64, n: u64) -> u64 {
        let mut r = 1;
        while e > 0 {
            if e & 1 == 1 {
                r = mulmod(r, a, n);
            }
            a = mulmod(a, a, n);
            e >>= 1;
        }
        r
    }
    if n < 2 {
        return false;
    }
    for p in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n % p == 0 {
            return n == p;
        }
    }
    let (mut d, mut s) = (n - 1, 0);
    while d % 2 == 0 {
        d /= 2;
        s += 1;
    }
    'outer: for a in [2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        // deterministic for every 64-bit n
        let mut x = powmod(a, d, n);
        if x == 1 || x == n - 1 {
            continue;
        }
        for _ in 0..s - 1 {
            x = mulmod(x, x, n);
            if x == n - 1 {
                continue 'outer;
            }
        }
        return false;
    }
    true
}

/// The `count` largest primes below 2^61.
fn primes(count: usize) -> Vec<Fp> {
    let mut out = Vec::new();
    let mut c = 1u64;
    while out.len() < count {
        let q = (1u64 << 61) - c;
        if is_prime(q) {
            out.push(Fp { q, c: c as u128 });
        }
        c += 2;
    }
    assert!(c < 1 << 20);
    out
}

// ---------------------------------------------------------------- one reduction step, exact

/// The dependencies with the pivots as free columns, modulo f: returns N[j][pos] for pos over order[..np]
/// (order = the support without the pivots, then the pivots).
fn null_mod(sc: &Scheme, d: usize, order: &[usize], k: usize, f: Fp) -> Vec<Vec<u64>> {
    let (r, c) = RC[d];
    let ns = order.len();
    let np = ns - k;
    // Gram matrices of the two other factors on the support, then their entrywise product
    let gram = |s: usize| -> Vec<Vec<u64>> {
        let cs = sc.cols(s);
        let sparse: Vec<Vec<(u32, u64)>> = order.iter().map(|&t| sc.x[s][t].iter().map(|&(i, v)| (i, f.of_q(v))).collect()).collect();
        let mut dense = vec![0u64; ns * cs];
        for (a, row) in sparse.iter().enumerate() {
            for &(i, v) in row {
                dense[a * cs + i as usize] = v;
            }
        }
        (0..ns)
            .into_par_iter()
            .map(|a| {
                (0..ns)
                    .map(|b| {
                        let rb = &dense[b * cs..(b + 1) * cs];
                        let (mut acc, mut cnt) = (0u128, 0);
                        for &(i, v) in &sparse[a] {
                            acc += v as u128 * rb[i as usize] as u128; // below 2^122
                            cnt += 1;
                            if cnt == 32 {
                                acc = f.red(acc) as u128;
                                cnt = 0;
                            }
                        }
                        f.red(acc)
                    })
                    .collect()
            })
            .collect()
    };
    let (gr, gc) = (gram(r), gram(c));
    let mut rows: Vec<Vec<u64>> = gr.into_par_iter().zip(gc.into_par_iter()).map(|(a, b)| a.iter().zip(&b).map(|(&x, &y)| f.mul(x, y)).collect()).collect();
    // forward elimination: every column of the support without the pivots must carry a pivot
    for col in 0..np {
        let i = (col..ns).find(|&i| rows[i][col] != 0).unwrap_or_else(|| panic!("modulo {}: column {col} of {np} has no pivot: the pivot products are not independent on the dependencies", f.q));
        rows.swap(col, i);
        let iv = f.inv(rows[col][col]);
        for v in rows[col][col..].iter_mut() {
            *v = f.mul(*v, iv);
        }
        let (top, rest) = rows.split_at_mut(col + 1);
        let pr = &top[col];
        rest.par_iter_mut().with_min_len(8).for_each(|row| {
            let x = row[col];
            if x != 0 {
                let cf = (f.q - x) as u128;
                for (v, &q) in row[col + 1..].iter_mut().zip(&pr[col + 1..]) {
                    *v = f.red(*v as u128 + cf * q as u128);
                }
                row[col] = 0;
            }
        });
    }
    assert!(rows[np..].iter().all(|r| r.iter().all(|&v| v == 0)), "modulo {}: the Gram matrix has rank above support - pivots", f.q);
    let rows = &rows[..np];
    (0..k)
        .into_par_iter()
        .map(|j| {
            let mut x = vec![0u64; ns];
            x[np + j] = 1;
            for i in (0..np).rev() {
                let row = &rows[i];
                let (mut acc, mut cnt) = (0u128, 0);
                for l in i + 1..ns {
                    if x[l] != 0 {
                        acc += row[l] as u128 * x[l] as u128;
                        cnt += 1;
                        if cnt == 32 {
                            acc = f.red(acc) as u128;
                            cnt = 0;
                        }
                    }
                }
                let a = f.red(acc);
                x[i] = if a == 0 { 0 } else { f.q - a };
            }
            x.truncate(np);
            x
        })
        .collect()
}

/// The rational n/d with |n|, d <= sqrt(M / 2) and n = x d modulo M (M = q0 q1), if there is one.
fn reconstruct(x: u128, m: u128) -> Option<Q> {
    if x == 0 {
        return Some(Q::ZERO);
    }
    let bound = ((m / 2) as f64).sqrt() as i128 - 2;
    let (mut r0, mut r1) = (m as i128, x as i128);
    let (mut t0, mut t1) = (0i128, 1i128);
    while r1 > bound {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (t0, t1) = (t1, t0 - q * t1);
    }
    if t1 == 0 || t1.abs() > bound || gcd(r1, t1) != 1 {
        return None;
    }
    Some(Q::new(if t1 < 0 { -r1 } else { r1 }, t1.abs()))
}

/// One step of a kronkill path: drop the pivot products of direction d, fold their slot-d factors into the others.
fn step(sc: &Scheme, d: usize, pivots: &[usize], support: Option<&[usize]>, ps: &[Fp]) -> (Scheme, Vec<usize>, String) {
    let t0 = Instant::now();
    let m = sc.m();
    let k = pivots.len();
    let mut is_piv = vec![false; m];
    for &j in pivots {
        assert!(j < m && !is_piv[j], "bad pivot {j}");
        is_piv[j] = true;
    }
    let all: Vec<usize> = (0..m).collect();
    let supp = support.unwrap_or(&all);
    let mut in_supp = vec![false; m];
    for &t in supp {
        in_supp[t] = true;
    }
    assert!(pivots.iter().all(|&j| in_supp[j]), "a pivot outside the support");
    let mut order: Vec<usize> = supp.iter().copied().filter(|&t| !is_piv[t]).collect();
    let np = order.len();
    order.extend_from_slice(pivots);
    let nm: Vec<Vec<Vec<u64>>> = ps.iter().map(|&f| null_mod(sc, d, &order, k, f)).collect();
    // lift from the first two primes, compare with the third
    let (f0, f1, f2) = (ps[0], ps[1], ps[2]);
    let modulus = f0.q as u128 * f1.q as u128;
    let q0_inv = f1.inv(f0.q % f1.q);
    let mut height = 1i64;
    let nq: Vec<Vec<Q>> = (0..k)
        .map(|j| {
            (0..np)
                .map(|pos| {
                    let (a0, a1) = (nm[0][j][pos], nm[1][j][pos]);
                    let diff = f1.red(a1 as u128 + (f1.q - a0 % f1.q) as u128);
                    let x = a0 as u128 + f0.q as u128 * f1.mul(diff, q0_inv) as u128;
                    let v = reconstruct(x, modulus).unwrap_or_else(|| panic!("dependency {j}, product {}: no rational of height below 2^60", order[pos]));
                    assert_eq!(f2.of_q(v), nm[2][j][pos], "dependency {j}, product {}: the lift disagrees with the third prime", order[pos]);
                    height = height.max(v.n.abs()).max(v.d);
                    v
                })
                .collect()
        })
        .collect();
    let nnz: usize = nq.iter().map(|r| r.iter().filter(|v| !v.is_zero()).count()).sum();
    // the fold, exact
    let cd = sc.cols(d);
    let fj: Vec<&Vec<(u32, Q)>> = pivots.iter().map(|&j| &sc.x[d][j]).collect();
    let folded: Vec<(usize, Vec<(u32, Q)>)> = (0..np)
        .into_par_iter()
        .filter(|&pos| (0..k).any(|j| !nq[j][pos].is_zero()))
        .map(|pos| {
            let mut row = vec![Q::ZERO; cd];
            for &(i, v) in &sc.x[d][order[pos]] {
                row[i as usize] = v;
            }
            for j in 0..k {
                let w = nq[j][pos];
                if !w.is_zero() {
                    for &(i, v) in fj[j] {
                        row[i as usize] = row[i as usize].sub(w.mul(v));
                    }
                }
            }
            (order[pos], row.into_iter().enumerate().filter(|e| !e.1.is_zero()).map(|(i, v)| (i as u32, v)).collect())
        })
        .collect();
    let mut newd: Vec<Option<Vec<(u32, Q)>>> = vec![None; m];
    for (t, row) in folded {
        newd[t] = Some(row);
    }
    let mut x: [Vec<Vec<(u32, Q)>>; 3] = [vec![], vec![], vec![]];
    let mut dead = Vec::new();
    for t in 0..m {
        if is_piv[t] {
            continue;
        }
        let rd = newd[t].take().unwrap_or_else(|| sc.x[d][t].clone());
        if rd.is_empty() {
            dead.push(t);
            continue;
        }
        for s in 0..3 {
            x[s].push(if s == d { rd.clone() } else { sc.x[s][t].clone() });
        }
    }
    let out = Scheme { n: sc.n, x };
    let msg = format!(
        "direction {d}: {k} dependencies on {} products (lifted from 2 primes of 61 bits, equal modulo a third; {nnz} nonzero coefficients, largest numerator or denominator {height}); {m} -> {} products ({k} pivots, {} left with a zero factor) ({:.1} s)",
        order.len(),
        out.m(),
        dead.len(),
        t0.elapsed().as_secs_f64()
    );
    (out, dead, msg)
}

// ---------------------------------------------------------------- the Brent equations, exact

struct Scaled {
    den: [i128; 3],
    rows: [Vec<Vec<(u32, i128)>>; 3],
    bits: f64,
}

/// Integer rows D_s x_s and a proof that sum_t |U_t[a] V_t[b] W_t[c]| stays below 2^126.
fn scale(sc: &Scheme) -> Scaled {
    let mut den = [1i128; 3];
    let mut mx = [0i128; 3];
    let mut rows: [Vec<Vec<(u32, i128)>>; 3] = [vec![], vec![], vec![]];
    for s in 0..3 {
        for row in &sc.x[s] {
            for &(_, v) in row {
                let g = gcd(den[s], v.d as i128);
                den[s] = (den[s] / g).checked_mul(v.d as i128).expect("the common denominator of a factor exceeds 127 bits");
            }
        }
        rows[s] = sc.x[s]
            .iter()
            .map(|row| {
                row.iter()
                    .map(|&(i, v)| {
                        let y = (den[s] / v.d as i128).checked_mul(v.n as i128).expect("a scaled entry exceeds 127 bits");
                        (i, y)
                    })
                    .collect()
            })
            .collect();
        mx[s] = rows[s].iter().flat_map(|r| r.iter().map(|e| e.1.abs())).max().unwrap_or(0);
    }
    let bits = (sc.m() as f64).log2() + mx.iter().map(|&v| (v.max(1) as f64).log2()).sum::<f64>();
    Scaled { den, rows, bits }
}

/// Number of Brent equations that fail (0 = the scheme is a matrix multiplication scheme over Q), and their count.
fn brent(sc: &Scheme) -> (u64, u64, String) {
    let t0 = Instant::now();
    let z = scale(sc);
    assert!(z.bits < 125.0, "partial sums could reach 2^{:.0}: beyond 128-bit integers", z.bits);
    let target = z.den[0].checked_mul(z.den[1]).and_then(|x| x.checked_mul(z.den[2])).expect("D_u D_v D_w exceeds 127 bits");
    let [n0, n1, n2] = sc.n;
    let (cu, cv, cw) = (n0 * n1, n1 * n2, n2 * n0);
    let mut by_col: Vec<Vec<(u32, i128)>> = vec![vec![]; cu];
    for (t, row) in z.rows[0].iter().enumerate() {
        for &(a, v) in row {
            by_col[a as usize].push((t as u32, v));
        }
    }
    let bad: u64 = (0..cu)
        .into_par_iter()
        .map(|a| {
            let mut acc = vec![0i128; cv * cw];
            for &(t, al) in &by_col[a] {
                let wr = &z.rows[2][t as usize];
                for &(b, be) in &z.rows[1][t as usize] {
                    let ab = al * be;
                    let line = &mut acc[b as usize * cw..(b as usize + 1) * cw];
                    for &(c, ga) in wr {
                        line[c as usize] += ab * ga;
                    }
                }
            }
            let (i, j) = (a / n1, a % n1);
            let mut bad = 0u64;
            for b in 0..cv {
                let (j2, k) = (b / n2, b % n2);
                for c in 0..cw {
                    let (k2, i2) = (c / n0, c % n0);
                    let want = if j == j2 && k == k2 && i == i2 { target } else { 0 };
                    if acc[b * cw + c] != want {
                        bad += 1;
                    }
                }
            }
            bad
        })
        .sum();
    let total = (cu * cv * cw) as u64;
    let msg = format!(
        "{bad} of {total} Brent equations fail; common denominators {:?}, partial sums below 2^{:.0} ({:.1} s)",
        z.den,
        z.bits.ceil(),
        t0.elapsed().as_secs_f64()
    );
    (bad, total, msg)
}

fn factor_small(mut v: i64) -> (Vec<i64>, i64) {
    let mut ps = Vec::new();
    let mut p = 2;
    while p * p <= v && p < 100_000 {
        if v % p == 0 {
            ps.push(p);
            while v % p == 0 {
                v /= p;
            }
        }
        p += 1;
    }
    if v > 1 && v < 10_000_000_000 {
        ps.push(v);
        v = 1;
    }
    (ps, v)
}

fn stats(sc: &Scheme) -> String {
    let mut out = Vec::new();
    let mut all_primes: Vec<i64> = Vec::new();
    for s in 0..3 {
        let nnz: usize = sc.x[s].iter().map(|r| r.len()).sum();
        let frac = sc.x[s].iter().flat_map(|r| r.iter()).filter(|e| e.1.d != 1).count();
        let maxd = sc.x[s].iter().flat_map(|r| r.iter()).map(|e| e.1.d).max().unwrap_or(1);
        let maxn = sc.x[s].iter().flat_map(|r| r.iter()).map(|e| e.1.n.abs()).max().unwrap_or(0);
        let mut dens: Vec<i64> = sc.x[s].iter().flat_map(|r| r.iter()).map(|e| e.1.d).collect();
        dens.sort_unstable();
        dens.dedup();
        for d in dens {
            let (ps, rest) = factor_small(d);
            all_primes.extend(ps);
            if rest > 1 {
                all_primes.push(-rest);
            }
        }
        out.push(format!("{} {nnz} nonzeros, {frac} fractions, largest numerator {maxn}, largest denominator {maxd}", ["u", "v", "w"][s]));
    }
    all_primes.sort_unstable();
    all_primes.dedup();
    let ring = if all_primes.is_empty() {
        "integer"
    } else if all_primes == [2] {
        "dyadic"
    } else {
        "rational"
    };
    format!("{}; denominator primes {:?} -> {ring}", out.join("; "), all_primes)
}

/// The exact check with its negative control.  Returns true when the scheme verifies and the control fails.
fn certify(sc: &Scheme, tag: &str) -> bool {
    let (bad, _, msg) = brent(sc);
    println!("  [{tag}] <{}x{}x{}:{}> {msg}", sc.n[0], sc.n[1], sc.n[2], sc.m());
    let mut c = sc.clone();
    let t = sc.m() / 2;
    let e = c.x[2][t][0];
    c.x[2][t][0] = (e.0, e.1.sub(Q { n: -1, d: 1 }));
    if c.x[2][t][0].1.is_zero() {
        c.x[2][t][0] = (e.0, Q { n: 2, d: 1 });
    }
    let (cbad, _, _) = brent(&c);
    println!("  [{tag}, one coefficient of product {t} changed] {cbad} equations fail -> {}", if cbad > 0 { "REJECTED" } else { "ACCEPTED: THE CHECK IS BROKEN" });
    bad == 0 && cbad > 0
}

// ---------------------------------------------------------------- constructions (build)

fn dims_of(n: [usize; 3], s: usize) -> (usize, usize) {
    match s {
        0 => (n[0], n[1]),
        1 => (n[1], n[2]),
        _ => (n[2], n[0]),
    }
}

/// Sort by column, add repeated columns, drop zeros.
fn tidy(mut r: Vec<(u32, Q)>) -> Vec<(u32, Q)> {
    r.sort_by_key(|e| e.0);
    let mut out: Vec<(u32, Q)> = Vec::with_capacity(r.len());
    for (i, q) in r {
        match out.last_mut() {
            Some(l) if l.0 == i => l.1 = l.1.add(q),
            _ => out.push((i, q)),
        }
    }
    out.retain(|e| !e.1.is_zero());
    out
}

/// <n0,n1,n2> -> <n1,n2,n0>: (u, v, w) -> (v, w, u); the layout is cyclic, no index changes.
fn rotate(sc: &Scheme) -> Scheme {
    let [u, v, w] = sc.x.clone();
    Scheme { n: [sc.n[1], sc.n[2], sc.n[0]], x: [v, w, u] }
}

/// <n0,n1,n2> -> <n0,n2,n1>: (u, v, w) -> (w^T, v^T, u^T).
fn transpose(sc: &Scheme) -> Scheme {
    let n = sc.n;
    // the source matrix is c x r (index b * r + a), the result r x c (index a * c + b)
    let tr = |rows: &Vec<Vec<(u32, Q)>>, r: usize, c: usize| -> Vec<Vec<(u32, Q)>> {
        rows.iter()
            .map(|row| {
                tidy(row
                    .iter()
                    .map(|&(i, q)| {
                        let (b, a) = (i as usize / r, i as usize % r);
                        ((a * c + b) as u32, q)
                    })
                    .collect())
            })
            .collect()
    };
    Scheme { n: [n[0], n[2], n[1]], x: [tr(&sc.x[2], n[0], n[2]), tr(&sc.x[1], n[2], n[1]), tr(&sc.x[0], n[1], n[0])] }
}

/// The same scheme with its dimensions in the order `target` (one of the six rotations / transposes).
fn orient(sc: &Scheme, target: [usize; 3]) -> Scheme {
    let plans: [&[u8]; 6] = [b"", b"r", b"rr", b"t", b"tr", b"trr"];
    for plan in plans {
        let mut t = sc.clone();
        for &o in plan {
            t = if o == b'r' { rotate(&t) } else { transpose(&t) };
        }
        if t.n == target {
            return t;
        }
    }
    panic!("no orientation of {:?} gives {:?}", sc.n, target);
}

/// The schoolbook scheme: one product per (i, j, k).
fn trivial(n: [usize; 3]) -> Scheme {
    let mut x: [Vec<Vec<(u32, Q)>>; 3] = [vec![], vec![], vec![]];
    let one = Q { n: 1, d: 1 };
    for i in 0..n[0] {
        for j in 0..n[1] {
            for k in 0..n[2] {
                x[0].push(vec![((i * n[1] + j) as u32, one)]);
                x[1].push(vec![((j * n[2] + k) as u32, one)]);
                x[2].push(vec![((k * n[0] + i) as u32, one)]);
            }
        }
    }
    Scheme { n, x }
}

/// Delete trailing indices until the dimensions are `target` (products left with a zero factor are dropped).
fn sub_to(sc: &Scheme, target: [usize; 3]) -> Scheme {
    let mut t = sc.clone();
    for s in 0..3 {
        assert!(t.n[s] >= target[s], "{:?} is not a sub-format of {:?}", target, sc.n);
        while t.n[s] > target[s] {
            t = project(&t, s, t.n[s] - 1);
        }
    }
    t
}

/// Direct sum along one axis: the parts agree on the other two dimensions.
fn direct_sum(parts: &[std::rc::Rc<Scheme>], axis: usize) -> Scheme {
    let mut n = parts[0].n;
    n[axis] = parts.iter().map(|p| p.n[axis]).sum();
    let mut x: [Vec<Vec<(u32, Q)>>; 3] = [vec![], vec![], vec![]];
    let mut off = [0usize; 3];
    for p in parts {
        for t in 0..3 {
            assert!(t == axis || p.n[t] == n[t], "direct sum along axis {axis}: {:?} against {:?}", p.n, n);
        }
        for s in 0..3 {
            let (r, c) = (s, (s + 1) % 3); // slot s is an n[s] x n[s + 1] matrix
            for row in &p.x[s] {
                x[s].push(row.iter().map(|&(i, q)| (((i as usize / p.n[c] + off[r]) * n[c] + i as usize % p.n[c] + off[c]) as u32, q)).collect());
            }
        }
        off[axis] += p.n[axis];
    }
    Scheme { n, x }
}

/// Kronecker product of two matrices given as sparse rows: (r1 x c1) (x) (r2 x c2).
fn kron_row(x: &[(u32, Q)], c1: usize, y: &[(u32, Q)], (r2, c2): (usize, usize)) -> Vec<(u32, Q)> {
    let mut out = Vec::with_capacity(x.len() * y.len());
    for &(i, a) in x {
        let (i1, j1) = (i as usize / c1, i as usize % c1);
        for &(j, b) in y {
            let (i2, j2) = (j as usize / c2, j as usize % c2);
            out.push((((i1 * r2 + i2) * (c1 * c2) + j1 * c2 + j2) as u32, a.mul(b)));
        }
    }
    out
}

fn kron_scheme(a: &Scheme, b: &Scheme) -> Scheme {
    let n = [a.n[0] * b.n[0], a.n[1] * b.n[1], a.n[2] * b.n[2]];
    let mut x: [Vec<Vec<(u32, Q)>>; 3] = [vec![], vec![], vec![]];
    for t in 0..a.m() {
        for q in 0..b.m() {
            for s in 0..3 {
                x[s].push(tidy(kron_row(&a.x[s][t], dims_of(a.n, s).1, &b.x[s][q], dims_of(b.n, s))));
            }
        }
    }
    Scheme { n, x }
}

/// y = sig x for sparse rows with the same support, else None.
fn ratio(x: &[(u32, Q)], y: &[(u32, Q)]) -> Option<Q> {
    if x.is_empty() || x.len() != y.len() {
        return None;
    }
    let sig = y[0].1.div(x[0].1);
    x.iter().zip(y).all(|(a, b)| a.0 == b.0 && a.1.mul(sig) == b.1).then_some(sig)
}

/// Block (r, c) of a matrix given as a sparse row with `cols` columns, the blocks being h x w.
fn block(row: &[(u32, Q)], cols: usize, r: usize, h: usize, c: usize, w: usize) -> Vec<(u32, Q)> {
    row.iter()
        .filter_map(|&(idx, q)| {
            let (rr, cc) = (idx as usize / cols, idx as usize % cols);
            (rr / h == r && cc / w == c).then(|| (((rr % h) * w + cc % w) as u32, q))
        })
        .collect()
}

/// A set of products of s1 whose sum is an image of the tensor <P,Q,R>:
///     sum over the members of u (x) v (x) w  =  sum over (i, j, k) of A_ij (x) B_jk (x) C_ki
/// with vectors A_ij, B_jk, C_ki of the three factor spaces of s1 (`vecs`, keyed by block coordinates).  Its
/// Kronecker product with <a,b,c> is then an image of <P a, Q b, R c>.  Nothing here is trusted: the scheme
/// that comes out is certified by the Brent check.
struct Block {
    ty: [usize; 3],
    members: Vec<usize>,
    vecs: [std::collections::BTreeMap<(usize, usize), Vec<(u32, Q)>>; 3],
    s3: std::rc::Rc<Scheme>,
}

/// The block of P Q R products laid out as the schoolbook products of <P,Q,R>: the product in cell (i, j, k)
/// has its first factor proportional to A_ij, its second to B_jk, its third to C_ki.
fn block_from_cells(s1: &Scheme, ty: [usize; 3], cells: &[(usize, [usize; 3])], s3: std::rc::Rc<Scheme>) -> Block {
    use std::collections::BTreeMap;
    let one = Q { n: 1, d: 1 };
    assert_eq!(cells.len(), ty[0] * ty[1] * ty[2], "a block of type {ty:?} needs every cell");
    let mut seen = std::collections::BTreeSet::new();
    for &(_, c) in cells {
        assert!((0..3).all(|d| c[d] < ty[d]) && seen.insert(c), "bad or repeated cell {c:?} in a block of type {ty:?}");
    }
    // slot p is an n[p] x n[p + 1] matrix: its block coordinates are (cell[p], cell[p + 1])
    let co = |p: usize, c: [usize; 3]| (c[p], c[(p + 1) % 3]);
    let mut rep: [BTreeMap<(usize, usize), usize>; 3] = Default::default();
    for p in 0..3 {
        for &(t, c) in cells {
            rep[p].entry(co(p, c)).or_insert(t);
        }
    }
    // product t = sigma_t A (x) B (x) C with A, B, C the representatives of its three block coordinates
    let sigma: Vec<Q> = cells
        .iter()
        .map(|&(t, c)| {
            (0..3).fold(one, |acc, p| {
                let r = rep[p][&co(p, c)];
                acc.mul(ratio(&s1.x[p][r], &s1.x[p][t]).unwrap_or_else(|| panic!("products {r} and {t} of s1 do not share their factor in slot {p}")))
            })
        })
        .collect();
    // sigma has to be carried by one slot: constant on that slot's block coordinates
    let mut scale: BTreeMap<(usize, usize), Q> = BTreeMap::new();
    let carrier = (0..3)
        .find(|&p| {
            scale.clear();
            cells.iter().zip(&sigma).all(|(&(_, c), &sg)| *scale.entry(co(p, c)).or_insert(sg) == sg)
        })
        .unwrap_or_else(|| panic!("the scalars of a block of type {ty:?} do not sit on one slot"));
    let mut vecs: [BTreeMap<(usize, usize), Vec<(u32, Q)>>; 3] = Default::default();
    for p in 0..3 {
        for (&rc, &t) in &rep[p] {
            let sg = if p == carrier { scale[&rc] } else { one };
            vecs[p].insert(rc, s1.x[p][t].iter().map(|&(i, q)| (i, q.mul(sg))).collect());
        }
    }
    Block { ty, members: cells.iter().map(|c| c.0).collect(), vecs, s3 }
}

/// The Kronecker product s1 (x) s2 in which, for every block, the products of its members with s2 are replaced
/// by one scheme s3 of <P a, Q b, R c>.  This is the serendipitous product (Smith; Sedoglavic; Perminov,
/// arXiv:2606.02480): a block is a set of products of s1 whose sum is an image of <P,Q,R>, e.g. g products
/// sharing one factor, or Perminov's Sect. 2.6.4 blocks with two non-unit dimensions.
fn shared_product(s1: &Scheme, s2: &Scheme, blocks: &[Block]) -> Scheme {
    let n = [s1.n[0] * s2.n[0], s1.n[1] * s2.n[1], s1.n[2] * s2.n[2]];
    let mut used = vec![false; s1.m()];
    for bl in blocks {
        for &t in &bl.members {
            assert!(!used[t], "product {t} of s1 is in two blocks");
            used[t] = true;
        }
    }
    let mut x: [Vec<Vec<(u32, Q)>>; 3] = [vec![], vec![], vec![]];
    for t in (0..s1.m()).filter(|&t| !used[t]) {
        for q in 0..s2.m() {
            for s in 0..3 {
                x[s].push(tidy(kron_row(&s1.x[s][t], dims_of(s1.n, s).1, &s2.x[s][q], dims_of(s2.n, s))));
            }
        }
    }
    for bl in blocks {
        let (ty, s3) = (bl.ty, &bl.s3);
        assert_eq!(s3.n, [s2.n[0] * ty[0], s2.n[1] * ty[1], s2.n[2] * ty[2]], "replacement scheme of the wrong format");
        for p in 0..3 {
            assert!(bl.vecs[p].keys().all(|&(r, c)| r < ty[p] && c < ty[(p + 1) % 3]), "block coordinates outside type {ty:?}");
        }
        for q in 0..s3.m() {
            for p in 0..3 {
                let c1 = dims_of(s1.n, p).1;
                let c3 = dims_of(s3.n, p).1;
                let (h, w) = dims_of(s2.n, p);
                let mut acc = Vec::new();
                for (&(r, c), v) in &bl.vecs[p] {
                    let b = block(&s3.x[p][q], c3, r, h, c, w);
                    acc.extend(kron_row(v, c1, &b, (h, w)));
                }
                x[p].push(tidy(acc));
            }
        }
    }
    // a product with a zero factor contributes nothing
    let keep: Vec<bool> = (0..x[0].len()).map(|t| (0..3).all(|s| !x[s][t].is_empty())).collect();
    for s in 0..3 {
        let mut it = keep.iter();
        x[s].retain(|_| *it.next().unwrap());
    }
    Scheme { n, x }
}

/// Executes a plan: {"defs": {name: node}, "out": node}.  Nodes:
///   {"op":"ref","name":S}  {"op":"file","path":P}  {"op":"trivial","n":[a,b,c]}
///   {"op":"orient","n":[a,b,c],"of":node}  {"op":"sub","n":[a,b,c],"of":node}
///   {"op":"rotate","of":node}     <n0,n1,n2> -> <n1,n2,n0>, the products in the same order
///   {"op":"transpose","of":node}  <n0,n1,n2> -> <n0,n2,n1>, the products in the same order
///   {"op":"sum","axis":i,"parts":[node,..]}  {"op":"prod","parts":[node,node]}
///   {"op":"shared","s1":node,"s2":node,"groups":[{"slot":s,"products":[..],"s3":node}
///                                              | {"type":[P,Q,R],"cells":[[product,i,j,k],..],"s3":node}
///                                              | {"type":[P,Q,R],"members":[..],"vectors":[[[r,c,[[index,value],..]],..] x 3],"s3":node}]}
struct Builder<'a> {
    defs: &'a serde_json::Map<String, Value>,
    memo: std::collections::HashMap<String, std::rc::Rc<Scheme>>,
    open: Vec<String>,
    /// directory of the plan file, for "here" file nodes
    dir: std::path::PathBuf,
    /// root of the scheme catalog, for "catalog" file nodes
    catalog: Option<String>,
}

/// Executes the plan file at `path`; returns the scheme and the plan (for its max_rank and note).
fn build_plan(path: &str, catalog: &Option<String>) -> (std::rc::Rc<Scheme>, Value) {
    let plan: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"))).expect("plan JSON");
    let empty = serde_json::Map::new();
    let dir = std::path::Path::new(path).parent().map(|p| p.to_path_buf()).unwrap_or_default();
    let mut b = Builder { defs: plan["defs"].as_object().unwrap_or(&empty), memo: Default::default(), open: vec![], dir, catalog: catalog.clone() };
    let sc = b.node(&plan["out"]);
    if let Some(mx) = plan["max_rank"].as_u64() {
        assert!(sc.m() as u64 <= mx, "rank {} above the plan's {mx}", sc.m());
    }
    (sc, plan)
}

impl Builder<'_> {
    fn node(&mut self, v: &Value) -> std::rc::Rc<Scheme> {
        use std::rc::Rc;
        let dims = |v: &Value| -> [usize; 3] {
            let a: Vec<usize> = v.as_array().expect("n").iter().map(|x| x.as_u64().unwrap() as usize).collect();
            [a[0], a[1], a[2]]
        };
        match v["op"].as_str().expect("a node needs an op") {
            "ref" => {
                let name = v["name"].as_str().unwrap().to_string();
                if let Some(s) = self.memo.get(&name) {
                    return s.clone();
                }
                assert!(!self.open.contains(&name), "the definition of {name} refers to itself");
                self.open.push(name.clone());
                let def = self.defs.get(&name).unwrap_or_else(|| panic!("no definition of {name}"));
                let s = self.node(def);
                self.open.pop();
                self.memo.insert(name, s.clone());
                s
            }
            "file" => {
                let path = if let Some(p) = v["catalog"].as_str() {
                    let root = self.catalog.as_ref().unwrap_or_else(|| panic!("the plan names the catalog file {p}: give the catalog's root with --catalog DIR"));
                    std::path::Path::new(root).join(p)
                } else if let Some(p) = v["here"].as_str() {
                    self.dir.join(p)
                } else {
                    std::path::PathBuf::from(v["path"].as_str().expect("a file node needs path, here or catalog"))
                };
                Rc::new(load(path.to_str().expect("UTF-8 path")))
            }
            "trivial" => Rc::new(trivial(dims(&v["n"]))),
            "orient" => {
                let s = self.node(&v["of"]);
                let n = dims(&v["n"]);
                if s.n == n { s } else { Rc::new(orient(&s, n)) }
            }
            "rotate" => Rc::new(rotate(&*self.node(&v["of"]))),
            "transpose" => Rc::new(transpose(&*self.node(&v["of"]))),
            "sub" => {
                let s = self.node(&v["of"]);
                let n = dims(&v["n"]);
                if s.n == n { s } else { Rc::new(sub_to(&s, n)) }
            }
            "sum" => {
                let parts: Vec<Rc<Scheme>> = v["parts"].as_array().unwrap().iter().map(|p| self.node(p)).collect();
                Rc::new(direct_sum(&parts, v["axis"].as_u64().unwrap() as usize))
            }
            "prod" => {
                let parts = v["parts"].as_array().unwrap();
                assert_eq!(parts.len(), 2);
                let (a, b) = (self.node(&parts[0]), self.node(&parts[1]));
                Rc::new(kron_scheme(&a, &b))
            }
            "shared" => {
                let (s1, s2) = (self.node(&v["s1"]), self.node(&v["s2"]));
                let groups: Vec<Block> = v["groups"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|g| {
                        let s3 = self.node(&g["s3"]);
                        let list = |v: &Value| -> Vec<usize> { v.as_array().unwrap().iter().map(|i| i.as_u64().unwrap() as usize).collect() };
                        if let Some(vs) = g["vectors"].as_array() {
                            // explicit vectors: per slot a list of [row block, column block, [[index, value], ..]]
                            assert_eq!(vs.len(), 3);
                            let mut vecs: [std::collections::BTreeMap<(usize, usize), Vec<(u32, Q)>>; 3] = Default::default();
                            for p in 0..3 {
                                let cols = s1.cols(p);
                                for e in vs[p].as_array().unwrap() {
                                    let row: Vec<(u32, Q)> = e[2].as_array().unwrap().iter().map(|x| (x[0].as_u64().unwrap() as u32, entry(&x[1]))).collect();
                                    assert!(row.iter().all(|x| (x.0 as usize) < cols), "vector index out of range");
                                    let old = vecs[p].insert((e[0].as_u64().unwrap() as usize, e[1].as_u64().unwrap() as usize), tidy(row));
                                    assert!(old.is_none(), "two vectors for one block coordinate");
                                }
                            }
                            Block { ty: dims(&g["type"]), members: list(&g["members"]), vecs, s3 }
                        } else if let Some(cells) = g["cells"].as_array() {
                            let cells: Vec<(usize, [usize; 3])> = cells.iter().map(|c| (c[0].as_u64().unwrap() as usize, dims(&json!([c[1], c[2], c[3]])))).collect();
                            block_from_cells(&s1, dims(&g["type"]), &cells, s3)
                        } else {
                            // g products sharing their factor in one slot: the blocks run along the dimension slot + 2
                            let d = (g["slot"].as_u64().unwrap() as usize + 2) % 3;
                            let prods = list(&g["products"]);
                            let mut ty = [1; 3];
                            ty[d] = prods.len();
                            let cells: Vec<(usize, [usize; 3])> = prods
                                .iter()
                                .enumerate()
                                .map(|(i, &t)| {
                                    let mut c = [0; 3];
                                    c[d] = i;
                                    (t, c)
                                })
                                .collect();
                            block_from_cells(&s1, ty, &cells, s3)
                        }
                    })
                    .collect();
                Rc::new(shared_product(&s1, &s2, &groups))
            }
            op => panic!("unknown op {op}"),
        }
    }
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let catalog: Option<String> = args.iter().position(|a| a == "--catalog").map(|i| {
        assert!(i + 1 < args.len(), "--catalog needs a directory");
        let d = args.remove(i + 1);
        args.remove(i);
        d
    });
    let mut flag = |key: &str| -> bool {
        match args.iter().position(|a| a == key) {
            Some(i) => {
                args.remove(i);
                true
            }
            None => false,
        }
    };
    let (check_input, dense) = (flag("--check-input"), flag("--dense"));
    let t0 = Instant::now();
    match args.first().map(|s| s.as_str()) {
        Some("check") if args.len() == 2 => {
            let sc = load(&args[1]);
            println!("{}: <{}x{}x{}:{}> loaded ({:.1} s)", args[1], sc.n[0], sc.n[1], sc.n[2], sc.m(), t0.elapsed().as_secs_f64());
            println!("  {}", stats(&sc));
            let ok = certify(&sc, "scheme");
            println!("  RESULT: {}", if ok { "VERIFIES EXACTLY; corrupted copy REJECTED" } else { "DOES NOT VERIFY" });
            std::process::exit(if ok { 0 } else { 1 });
        }
        Some("replay") if args.len() == 4 => {
            let pj: Value = serde_json::from_str(&std::fs::read_to_string(&args[2]).expect("path file")).expect("path JSON");
            let from_plan = args[1].ends_with("plan.json");
            let mut sc = if from_plan {
                let (s, _) = build_plan(&args[1], &catalog);
                std::rc::Rc::try_unwrap(s).unwrap_or_else(|rc| Scheme { n: rc.n, x: rc.x.clone() })
            } else {
                load(&args[1])
            };
            println!("{}: <{}x{}x{}:{}> {} ({:.1} s); path {} (sequence {:?})", args[1], sc.n[0], sc.n[1], sc.n[2], sc.m(), if from_plan { "built" } else { "loaded" }, t0.elapsed().as_secs_f64(), args[2], pj["sequence"].as_str().unwrap_or(""));
            if check_input {
                assert!(certify(&sc, "input"), "the input does not verify");
            }
            let ps = primes(3);
            println!("  primes {:?}", ps.iter().map(|f| f.q).collect::<Vec<_>>());
            for (si, st) in pj["stages"].as_array().unwrap().iter().enumerate() {
                let del = st["delete"].as_str().unwrap();
                if !del.is_empty() {
                    let slot = "IJK".find(&del[..1]).expect("bad deletion");
                    let m_in = sc.m();
                    sc = project(&sc, slot, del[1..].parse().expect("bad deletion"));
                    println!("  stage {si}: delete {del}: {m_in} -> {} products, <{}x{}x{}>", sc.m(), sc.n[0], sc.n[1], sc.n[2]);
                    assert_eq!(sc.m() as u64, st["alive"].as_u64().unwrap(), "survivors differ from kronkill's");
                }
                for (ti, x) in st["steps"].as_array().unwrap().iter().enumerate() {
                    let list = |v: &Value| -> Vec<usize> { v.as_array().unwrap().iter().map(|i| i.as_u64().unwrap() as usize).collect() };
                    assert_eq!(x["m"].as_u64().unwrap() as usize, sc.m());
                    let pivots = list(&x["pivots"]);
                    let support = x.get("support").filter(|v| v.is_array()).map(list);
                    let (y, dead, msg) = step(&sc, x["direction"].as_u64().unwrap() as usize, &pivots, support.as_deref(), &ps);
                    println!("  stage {si} step {ti}: {msg}");
                    assert_eq!(y.m() as u64, x["m_out"].as_u64().unwrap(), "product count differs from kronkill's");
                    assert_eq!(dead, list(&x["also_zero"]), "the products left with a zero factor differ from kronkill's");
                    sc = y;
                }
            }
            assert_eq!(sc.m() as u64, pj["m_out"].as_u64().unwrap());
            println!("  {}", stats(&sc));
            let ok = certify(&sc, "output");
            if ok {
                save(&sc, &args[3], dense, json!({"source": args[1], "path": args[2], "sequence": pj["sequence"], "by": "kronexact replay"}));
                println!("  RESULT: output with {} products VERIFIES EXACTLY; corrupted copy REJECTED; written {} ({:.1} s)", sc.m(), args[3], t0.elapsed().as_secs_f64());
            } else {
                println!("  RESULT: DOES NOT VERIFY; nothing written");
            }
            std::process::exit(if ok { 0 } else { 1 });
        }
        Some("build") if args.len() == 3 => {
            let (sc, plan) = build_plan(&args[1], &catalog);
            println!("{}: built <{}x{}x{}:{}> ({:.1} s)", args[1], sc.n[0], sc.n[1], sc.n[2], sc.m(), t0.elapsed().as_secs_f64());
            println!("  {}", stats(&sc));
            let ok = certify(&sc, "output");
            if ok {
                save(&sc, &args[2], dense, plan["note"].clone());
                println!("  RESULT: output with {} products VERIFIES EXACTLY; corrupted copy REJECTED; written {} ({:.1} s)", sc.m(), args[2], t0.elapsed().as_secs_f64());
            } else {
                println!("  RESULT: DOES NOT VERIFY; nothing written");
            }
            std::process::exit(if ok { 0 } else { 1 });
        }
        _ => {
            eprintln!("usage: kronexact check SCHEME.json\n       kronexact replay SOURCE.json PATH.json OUT.json [--check-input] [--dense] [--catalog DIR]\n       kronexact build PLAN.json OUT.json [--dense] [--catalog DIR]");
            std::process::exit(2);
        }
    }
}
