//! bpcse — Boyar–Peralta-style cancellation-aware CSE for dyadic
//! linear maps (the DPS <4x4x4:48> networks). Global greedy: keep a
//! base S of signals (inputs first); repeatedly add the candidate
//! w = 2^a·u ± 2^b·v (u,v ∈ S) that most reduces the total target
//! distance, where dist(t) ∈ {0: done, 1: t = ±2^e·s, 2: t solvable
//! as a dyadic-monomial pair over S, 9: far}. Cancellation is native
//! (signed combos). Emits a PLinOpt-syntax SLP; SLPchecker referees
//! the official count.
//!
//! Usage: bpcse M.sms out.slp [--iters N] [--cands N] [--seed S]
//!        [--threads T]
use rayon::prelude::*;
use std::sync::atomic::{AtomicUsize, Ordering};

type V = Vec<i64>;

fn parse_sms(path: &str) -> (usize, usize, Vec<V>) {
    let txt = std::fs::read_to_string(path).expect("sms");
    let mut rows = 0usize;
    let mut cols = 0usize;
    let mut m: Vec<V> = Vec::new();
    for ln in txt.lines() {
        let f: Vec<&str> = ln.split_whitespace().collect();
        if f.is_empty() || f[0].starts_with('#') {
            continue;
        }
        if m.is_empty() && f.len() >= 2 && f[2..].iter().all(|_| true) && rows == 0 {
            rows = f[0].parse().unwrap();
            cols = f[1].parse().unwrap();
            m = vec![vec![0; cols]; rows];
            continue;
        }
        let (i, j): (usize, usize) = (f[0].parse().unwrap(), f[1].parse().unwrap());
        if i == 0 {
            break;
        }
        // dyadic value scaled by 8 -> integer
        let v = f[2];
        let x: i64 = if let Some((n, d)) = v.split_once('/') {
            let n: i64 = n.parse().unwrap();
            let d: i64 = d.parse().unwrap();
            n * 8 / d
        } else {
            v.parse::<i64>().unwrap() * 8
        };
        m[i - 1][j - 1] = x;
    }
    (rows, cols, m)
}

fn is_zero(v: &V) -> bool {
    v.iter().all(|&x| x == 0)
}

/// t == alpha * s for alpha = ±2^e (e in -6..=6)? return alpha as (num,den2)
fn scale_match(t: &V, s: &V) -> Option<(i64, i64)> {
    let mut ratio: Option<(i64, i64)> = None; // t = num/den * s
    for i in 0..t.len() {
        match (t[i], s[i]) {
            (0, 0) => {}
            (0, _) | (_, 0) => return None,
            (a, b) => {
                let (num, den) = (a, b);
                if let Some((n0, d0)) = ratio {
                    if num as i128 * d0 as i128 != n0 as i128 * den as i128 {
                        return None;
                    }
                } else {
                    ratio = Some((num, den));
                }
            }
        }
    }
    let (n, d) = ratio?;
    // n/d must be ±2^e; return REDUCED with one side = 1
    let (mut n, mut d) = (n, d);
    if d < 0 {
        n = -n;
        d = -d;
    }
    let mut a = n.unsigned_abs();
    let mut b = d.unsigned_abs();
    if a == 0 || b == 0 {
        return None;
    }
    let g = {
        let (mut x, mut y) = (a, b);
        while y != 0 {
            let r = x % y;
            x = y;
            y = r;
        }
        x
    };
    a /= g;
    b /= g;
    if (a & (a - 1)) != 0 || (b & (b - 1)) != 0 || a > 64 || b > 64 {
        return None;
    }
    Some((if n < 0 { -(a as i64) } else { a as i64 }, b as i64))
}

/// t = alpha*u + beta*v with alpha,beta = ±2^e? solve on pivot coords
fn pair_solve(t: &V, u: &V, v: &V) -> bool {
    let n = t.len();
    // find pivot pair with nonzero det
    for p in 0..n {
        for q in (p + 1)..n {
            let det = (u[p] as i128) * (v[q] as i128) - (u[q] as i128) * (v[p] as i128);
            if det == 0 {
                continue;
            }
            // alpha = (t_p v_q - t_q v_p)/det ; beta = (u_p t_q - u_q t_p)/det
            let an = (t[p] as i128) * (v[q] as i128) - (t[q] as i128) * (v[p] as i128);
            let bn = (u[p] as i128) * (t[q] as i128) - (u[q] as i128) * (t[p] as i128);
            let ok = |num: i128, den: i128| -> Option<f64> {
                if num == 0 {
                    return Some(0.0);
                }
                let (mut a, mut b) = (num.unsigned_abs(), den.unsigned_abs());
                let g = {
                    let (mut x, mut y) = (a, b);
                    while y != 0 {
                        let r = x % y;
                        x = y;
                        y = r;
                    }
                    x
                };
                a /= g;
                b /= g;
                if (a & (a - 1)) == 0 && (b & (b - 1)) == 0 && a <= 64 && b <= 64 {
                    Some(1.0)
                } else {
                    None
                }
            };
            if ok(an, det).is_none() || ok(bn, det).is_none() {
                return false;
            }
            // full verify: alpha = an/det, beta = bn/det
            for i in 0..n {
                let lhs = (t[i] as i128) * det;
                let rhs = an * (u[i] as i128) + bn * (v[i] as i128);
                if lhs != rhs {
                    return false;
                }
            }
            return true;
        }
    }
    false
}

/// pair_solve returning the dyadic-monomial coefficients (an/det, bn/det)
fn pair_solve_coef(t: &V, u: &V, v: &V) -> Option<((i64, i64), (i64, i64))> {
    let n = t.len();
    for p in 0..n {
        for q in (p + 1)..n {
            let det = (u[p] as i128) * (v[q] as i128) - (u[q] as i128) * (v[p] as i128);
            if det == 0 {
                continue;
            }
            let an = (t[p] as i128) * (v[q] as i128) - (t[q] as i128) * (v[p] as i128);
            let bn = (u[p] as i128) * (t[q] as i128) - (u[q] as i128) * (t[p] as i128);
            for i in 0..n {
                if (t[i] as i128) * det != an * (u[i] as i128) + bn * (v[i] as i128) {
                    return None;
                }
            }
            let red = |num: i128, den: i128| -> Option<(i64, i64)> {
                if num == 0 {
                    return Some((0, 1));
                }
                let neg = (num < 0) != (den < 0);
                let (mut a, mut b) = (num.unsigned_abs(), den.unsigned_abs());
                let g = {
                    let (mut x, mut y) = (a, b);
                    while y != 0 {
                        let r = x % y;
                        x = y;
                        y = r;
                    }
                    x
                };
                a /= g;
                b /= g;
                if (a & (a.wrapping_sub(1))) != 0 || (b & (b.wrapping_sub(1))) != 0
                    || a > 64 || b > 64 {
                    return None;
                }
                Some((if neg { -(a as i64) } else { a as i64 }, b as i64))
            };
            return match (red(an, det), red(bn, det)) {
                (Some(x), Some(y)) => Some((x, y)),
                _ => None,
            };
        }
    }
    None
}

fn coef_str(name: &str, num: i64, den: i64, lead: bool) -> String {
    let mag = num.abs();
    let sgn = if num < 0 { "-" } else if lead { "" } else { "+" };
    if den == 1 && mag == 1 {
        format!("{sgn}{name}")
    } else if den == 1 {
        format!("{sgn}{name}*{mag}")
    } else if mag == 1 {
        format!("{sgn}{name}/{den}")
    } else {
        format!("{sgn}{name}*{mag}/{den}")
    }
}

fn dist(t: &V, base: &[V]) -> u8 {
    for s in base {
        if scale_match(t, s).is_some() {
            return 1;
        }
    }
    for i in 0..base.len() {
        for j in (i + 1)..base.len() {
            if pair_solve(t, &base[i], &base[j]) {
                return 2;
            }
        }
    }
    9
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let inpath = &args[1];
    let outpath = &args[2];
    let get = |flag: &str, d: i64| -> i64 {
        args.iter()
            .position(|a| a == flag)
            .and_then(|i| args.get(i + 1))
            .and_then(|v| v.parse().ok())
            .unwrap_or(d)
    };
    let iters = get("--iters", 200) as usize;
    let ncand = get("--cands", 30000) as usize;
    let seed0 = get("--seed", 1) as u64;
    let threads = get("--threads", 4) as usize;
    let _ = rayon::ThreadPoolBuilder::new()
        .num_threads(threads)
        .build_global();

    let (rows, cols, targets) = parse_sms(inpath);
    eprintln!("bpcse: {rows} targets, {cols} inputs");

    // base: inputs (unit vectors), emitted names i0..i{cols-1}
    let mut base: Vec<V> = (0..cols)
        .map(|j| {
            let mut v = vec![0i64; cols];
            v[j] = 8; // inputs carry the x8 scaling convention
            v
        })
        .collect();
    let mut names: Vec<String> = (0..cols).map(|j| format!("i{j}")).collect();
    let mut ops: Vec<String> = Vec::new();
    let mut nadd = 0usize;
    let mut nmul = 0usize;

    let pm1 = args.iter().any(|a| a == "--pm1");
    let lams_all: [(i64, i64); 10] = [
        (1, 1), (-1, 1), (2, 1), (-2, 1), (4, 1), (-4, 1),
        (1, 2), (-1, 2), (1, 4), (-1, 4),
    ];
    let lams: &[(i64, i64)] = if pm1 { &lams_all[..2] } else { &lams_all[..] };

    let mut dists: Vec<u8> = targets.iter().map(|t| dist(t, &base)).collect();
    let mut rng = 0x9e3779b97f4a7c15u64 ^ seed0;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng
    };
    let tcount = AtomicUsize::new(0);

    for it in 0..iters {
        let total: u32 = dists.iter().map(|&d| d as u32).sum();
        if dists.iter().all(|&d| d <= 1) {
            break;
        }
        // candidate pool: sampled pairs x lambdas (always include pairs
        // with the most-recent base signal for locality)
        let nb = base.len();
        let mut cands: Vec<(usize, usize, usize)> = Vec::with_capacity(ncand);
        for j in 0..nb.saturating_sub(1) {
            for (li, _) in lams.iter().enumerate() {
                cands.push((nb - 1, j, li));
            }
        }
        while cands.len() < ncand {
            let a = (next() % nb as u64) as usize;
            let b = (next() % nb as u64) as usize;
            if a == b {
                continue;
            }
            let li = (next() % lams.len() as u64) as usize;
            cands.push((a, b, li));
        }
        // score in parallel: new total distance if w added
        let scored: Vec<(u32, usize)> = cands
            .par_iter()
            .enumerate()
            .filter_map(|(ci, &(a, b, li))| {
                let (ln, ld) = lams[li];
                let mut w: V = vec![0; cols];
                for i in 0..cols {
                    let x = base[a][i] as i128 * ld as i128 + base[b][i] as i128 * ln as i128;
                    if x.abs() > i64::MAX as i128 / 4 {
                        return None;
                    }
                    w[i] = x as i64;
                }
                if is_zero(&w) {
                    return None;
                }
                let mut newtot = 0u32;
                for (ti, t) in targets.iter().enumerate() {
                    let od = dists[ti];
                    if od <= 1 {
                        newtot += od as u32;
                        continue;
                    }
                    let mut nd = od;
                    if scale_match(t, &w).is_some() {
                        nd = 1;
                    } else if od > 2 {
                        // pair with w?
                        if base.iter().any(|s| pair_solve(t, &w, s)) {
                            nd = 2;
                        }
                    }
                    newtot += nd.min(od) as u32;
                }
                tcount.fetch_add(1, Ordering::Relaxed);
                if newtot < total {
                    Some((newtot, ci))
                } else {
                    None
                }
            })
            .collect();
        let Some(&(besttot, ci)) = scored.iter().min_by_key(|(t, _)| *t) else {
            break; // no improving candidate
        };
        let (a, b, li) = cands[ci];
        let (ln, ld) = lams[li];
        let mut w: V = vec![0; cols];
        for i in 0..cols {
            w[i] = (base[a][i] as i128 * ld as i128 + base[b][i] as i128 * ln as i128) as i64;
        }
        // emit: t_new := (base[a])*ld + base[b]*ln  (in x8 space the
        // shared scaling cancels in the checker's projective view; we
        // emit the literal integer relation using shifts)
        let nm = format!("t{}", names.len());
        let term = |c: i64, n: &str| -> String {
            match c {
                1 => n.to_string(),
                -1 => format!("-{n}"),
                2 => format!("{n}*2"),
                -2 => format!("-{n}*2"),
                4 => format!("{n}*4"),
                -4 => format!("-{n}*4"),
                _ => unreachable!(),
            }
        };
        let (ca, cb) = (ld, ln);
        let expr = if cb >= 0 {
            format!("{}+{}", term(ca, &names[a]), term(cb, &names[b]))
        } else {
            format!("{}{}", term(ca, &names[a]), term(cb, &names[b]))
        };
        ops.push(format!("{nm}:={expr};"));
        nadd += 1;
        nmul += (ca.abs() > 1) as usize + (cb.abs() > 1) as usize;
        base.push(w);
        names.push(nm);
        // refresh distances
        for (ti, t) in targets.iter().enumerate() {
            if dists[ti] > 0 {
                dists[ti] = dist(t, &base).min(dists[ti]);
            }
        }
        eprintln!(
            "[{it}] base {}  Sigma-dist {} -> {besttot}  (adds {nadd} muls {nmul})",
            base.len(),
            total
        );
    }
    eprintln!(
        "greedy done: dists {:?}",
        dists.iter().fold([0usize; 10], |mut h, &d| {
            h[d as usize] += 1;
            h
        })
    );
    // ---- assembly: emit each target as oN ----
    for (ti, t) in targets.iter().enumerate() {
        // dist 1: single scale
        let mut done = false;
        for (si, sv) in base.iter().enumerate() {
            if let Some((n, d)) = scale_match(t, sv) {
                ops.push(format!("o{ti}:={};", coef_str(&names[si], n, d, true)));
                nmul += (n.abs() != 1 || d != 1) as usize;
                done = true;
                break;
            }
        }
        if done {
            continue;
        }
        // dist 2: solved pair
        'outer: for i in 0..base.len() {
            for j in (i + 1)..base.len() {
                if let Some(((an, ad), (bn, bd))) = pair_solve_coef(t, &base[i], &base[j]) {
                    if an == 0 || bn == 0 {
                        continue;
                    }
                    ops.push(format!(
                        "o{ti}:={}{};",
                        coef_str(&names[i], an, ad, true),
                        coef_str(&names[j], bn, bd, false)
                    ));
                    nadd += 1;
                    nmul += (an.abs() != 1 || ad != 1) as usize
                        + (bn.abs() != 1 || bd != 1) as usize;
                    done = true;
                    break 'outer;
                }
            }
        }
        if done {
            continue;
        }
        // fallback: entrywise decomposition over inputs
        let mut acc: Option<String> = None;
        for (j, &c) in t.iter().enumerate() {
            if c == 0 {
                continue;
            }
            // c is in x8 space: real coefficient c/8
            let (num, den) = {
                let mut n = c;
                let mut d = 8i64;
                while n % 2 == 0 && d > 1 {
                    n /= 2;
                    d /= 2;
                }
                (n, d)
            };
            let piece = coef_str(&format!("i{j}"), num, den, acc.is_none());
            acc = Some(match acc {
                None => piece,
                Some(prev) => {
                    let nm = format!("t{}", names.len() + 1000 + ti * 64 + j);
                    ops.push(format!("{nm}:={prev}{piece};"));
                    nadd += 1;
                    nmul += (num.abs() != 1 || den != 1) as usize;
                    nm
                }
            });
        }
        ops.push(format!("o{ti}:={};", acc.unwrap()));
    }
    println!("bpcse emitted: {} ops ({nadd} adds, {nmul} shift-muls) -> {outpath}", ops.len());
    std::fs::write(outpath, ops.join("\n") + "\n").unwrap();
}
