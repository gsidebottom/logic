//! pcxl — experiment (a): exact degree-D Polynomial Calculus closure of
//! the Brent system over F_2 (Boolean ring: monomials are multilinear,
//! x^2 = x built into multiplication).
//!
//! PC with degree bound D: lines are polynomials of degree <= D; rules are
//! F_2-linear combination and multiplication by a variable when the
//! result stays within degree D. The set of derivable polynomials is the
//! fixpoint of: echelon-reduce, multiply every basis row by every
//! variable (keeping results of degree <= D), insert. The system is
//! refuted at degree D iff the constant 1 is derived. This is the exact
//! degree-D closure (Macaulay-matrix / XL iterated to a fixpoint), unlike
//! a degree-capped Buchberger run, which is only an upper bound.
//!
//!   pcxl --n 3 --r 2 --deg 4 [--max-rows 4000000] [--time 600]
//! prints REFUTED / OPEN (closure complete, 1 not derived) / CAP.
use std::collections::HashMap;
use std::time::Instant;

/// monomial: up to 6 variables, 10 bits each (index+1), ascending, packed
/// low-to-high; 0 = the constant 1.
type Mono = u64;

fn mono_vars(m: Mono) -> Vec<u32> {
    let mut v = Vec::new();
    let mut x = m;
    while x != 0 {
        v.push((x & 1023) as u32 - 1);
        x >>= 10;
    }
    v
}
fn mono_from(vars: &[u32]) -> Mono {
    let mut m: Mono = 0;
    for (k, &v) in vars.iter().enumerate() {
        m |= ((v as u64) + 1) << (10 * k);
    }
    m
}
fn mono_deg(m: Mono) -> usize {
    let mut d = 0;
    let mut x = m;
    while x != 0 {
        d += 1;
        x >>= 10;
    }
    d
}
fn mono_mul_var(m: Mono, x: u32) -> Mono {
    let mut vs = mono_vars(m);
    if vs.contains(&x) {
        return m;
    }
    vs.push(x);
    vs.sort_unstable();
    mono_from(&vs)
}

/// polynomial = sorted distinct monomials (XOR-set); pivot = last (max)
type Poly = Vec<Mono>;

fn poly_add(a: &Poly, b: &Poly) -> Poly {
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut i, mut j) = (0, 0);
    while i < a.len() && j < b.len() {
        if a[i] < b[j] {
            out.push(a[i]);
            i += 1;
        } else if a[i] > b[j] {
            out.push(b[j]);
            j += 1;
        } else {
            i += 1;
            j += 1;
        }
    }
    out.extend_from_slice(&a[i..]);
    out.extend_from_slice(&b[j..]);
    out
}
fn poly_mul_var(p: &Poly, x: u32) -> Poly {
    let mut ms: Vec<Mono> = p.iter().map(|&m| mono_mul_var(m, x)).collect();
    ms.sort_unstable();
    // cancel pairs
    let mut out = Vec::with_capacity(ms.len());
    let mut i = 0;
    while i < ms.len() {
        if i + 1 < ms.len() && ms[i] == ms[i + 1] {
            i += 2;
        } else {
            out.push(ms[i]);
            i += 1;
        }
    }
    out
}
fn poly_deg(p: &Poly) -> usize {
    p.iter().map(|&m| mono_deg(m)).max().unwrap_or(0)
}

struct Basis {
    rows: HashMap<Mono, Poly>, // pivot -> row
}
impl Basis {
    fn reduce(&self, mut p: Poly) -> Poly {
        loop {
            let Some(&piv) = p.last() else { return p };
            match self.rows.get(&piv) {
                Some(r) => p = poly_add(&p, r),
                None => return p,
            }
        }
    }
}

fn brent_polys(n: usize, r: usize) -> (usize, Vec<Poly>) {
    // variables: alpha m (i,j) = m*3nn... layout: per product m: a(nn) b(nn) g(nn)
    let nn = n * n;
    let va = |m: usize, i: usize, j: usize| (m * 3 * nn + i * n + j) as u32;
    let vb = |m: usize, i: usize, j: usize| (m * 3 * nn + nn + i * n + j) as u32;
    let vg = |m: usize, i: usize, j: usize| (m * 3 * nn + 2 * nn + i * n + j) as u32;
    let mut polys = Vec::new();
    for a in 0..n {
        for b in 0..n {
            for c in 0..n {
                for d in 0..n {
                    for p in 0..n {
                        for q in 0..n {
                            let mut ms: Vec<Mono> = (0..r)
                                .map(|m| {
                                    let mut vs = vec![va(m, a, b), vb(m, c, d), vg(m, p, q)];
                                    vs.sort_unstable();
                                    mono_from(&vs)
                                })
                                .collect();
                            if b == c && a == p && d == q {
                                ms.push(0); // + 1
                            }
                            ms.sort_unstable();
                            polys.push(ms);
                        }
                    }
                }
            }
        }
    }
    (3 * nn * r, polys)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |k: &str, d: usize| -> usize {
        args.iter().position(|a| a == k).and_then(|i| args.get(i + 1)).and_then(|v| v.parse().ok()).unwrap_or(d)
    };
    let n = get("--n", 3);
    let r = get("--r", 2);
    let deg = get("--deg", 4);
    let max_rows = get("--max-rows", 4_000_000);
    let time_s = get("--time", 600) as f64;
    assert!(deg <= 6, "monomial encoding supports degree <= 6");
    let (nvars, axioms) = brent_polys(n, r);
    let t0 = Instant::now();
    let mut basis = Basis { rows: HashMap::new() };
    // queue of polynomials to insert; each inserted row is multiplied by all vars once
    let mut queue: Vec<Poly> = axioms;
    let mut inserted = 0usize;
    let mut multiplied = 0usize;
    let mut refuted = false;
    let mut capped = false;
    let mut pending_mul: Vec<Poly> = Vec::new();
    loop {
        while let Some(p) = queue.pop() {
            let p = basis.reduce(p);
            if p.is_empty() {
                continue;
            }
            if p.len() == 1 && p[0] == 0 {
                refuted = true;
                break;
            }
            let piv = *p.last().unwrap();
            basis.rows.insert(piv, p.clone());
            inserted += 1;
            pending_mul.push(p);
            if inserted >= max_rows || t0.elapsed().as_secs_f64() > time_s {
                capped = true;
                break;
            }
        }
        if refuted || capped || pending_mul.is_empty() {
            break;
        }
        // multiply pending rows by every variable (degree-bounded)
        let rows = std::mem::take(&mut pending_mul);
        for p in &rows {
            let d = poly_deg(p);
            for x in 0..nvars as u32 {
                if d < deg {
                    queue.push(poly_mul_var(p, x));
                } else {
                    let q = poly_mul_var(p, x);
                    if poly_deg(&q) <= deg {
                        queue.push(q);
                    }
                }
                multiplied += 1;
            }
            if t0.elapsed().as_secs_f64() > time_s {
                capped = true;
                break;
            }
        }
        if capped {
            break;
        }
    }
    let verdict = if refuted { "REFUTED" } else if capped { "CAP" } else { "OPEN" };
    println!(
        "pcxl n={n} r={r} deg={deg}: {verdict}  rows={inserted} products={multiplied} vars={nvars} {:.1}s",
        t0.elapsed().as_secs_f64()
    );
}
