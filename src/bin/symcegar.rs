//! Propose-and-block server for the cyclic-quotient 50 question: is
//! there a cyclic-invariant rank-23 scheme (the quotient's orbit ansatz)
//! whose A-leg costs at most L additions?  Per-step is 3a+14, so L = 12
//! is the 50.
//!
//! One persistent CaDiCaL solver holds
//!   * the quotient Brent CNF (variables = the 23 A-blocks);
//!   * lex constraints breaking the RELABELING symmetry only: each
//!     3-orbit rotated so its first block is lex-least, orbits sorted,
//!     fixed products sorted.  Relabeling never changes the scheme, so
//!     the A-row set and its leg cost are invariant: every scheme keeps
//!     a representative;
//!   * indicators y_v (v = 1..511), forced true when some A-block
//!     equals v, and a sequential counter  sum y_v <= dmax  (a leg with
//!     d distinct rows costs at least d-9, so dmax = L+9).
//!
//! The driver (matmul/symcegar.py) speaks one command per line:
//!   solve [secs]       -> "b <621 bits>" | "s UNSAT" | "s UNKNOWN" (budget
//!                         spent; learned clauses persist into the next call)
//!   block v1 .. vk     -> adds (-y_v1 | .. | -y_vk): no A-row set may
//!                         contain all of v1..vk (sound when that set
//!                         costs more than L: cost is monotone under
//!                         inclusion); replies "ok"
//!   check <207 chars>  -> solve assuming the A-bits ('0'/'1'/'-' free);
//!                         "s SAT" | "s UNSAT"
//!   stats              -> solver counters
//!
//! usage: symcegar cnf map [--dmax D] [--seed N] [--shuffle S] [--no-lex]
//!          [--pin file]   (207 chars '0'/'1'/'-': fixes A-bits, for gates)

use logic::cadical;
use std::io::{BufRead, Write};

type Solver = cadical::Solver;

fn arg_val<T: std::str::FromStr>(args: &[String], key: &str) -> Option<T> {
    args.iter()
        .position(|a| a == key)
        .and_then(|i| args.get(i + 1))
        .and_then(|s| s.parse().ok())
}

/// x <=_lex y, most significant position first.
fn lex_le(s: &mut Solver, x: &[i32], y: &[i32], next: &mut i32) -> usize {
    let mut added = 0;
    let mut eq: Option<i32> = None;
    for i in 0..x.len() {
        let (a, b) = (x[i], y[i]);
        let mut c = vec![-a, b];
        c.extend(eq.map(|e| -e));
        s.add_clause(c);
        added += 1;
        if i + 1 < x.len() {
            let e2 = *next;
            *next += 1;
            let mut c1 = vec![-a, -b, e2];
            c1.extend(eq.map(|e| -e));
            let mut c2 = vec![a, b, e2];
            c2.extend(eq.map(|e| -e));
            s.add_clause(c1);
            s.add_clause(c2);
            added += 2;
            eq = Some(e2);
        }
    }
    added
}

/// Sinz sequential counter: at most k of xs.
fn at_most(s: &mut Solver, xs: &[i32], k: usize, next: &mut i32) -> usize {
    let n = xs.len();
    if k >= n {
        return 0;
    }
    if k == 0 {
        for &x in xs {
            s.add_clause([-x]);
        }
        return n;
    }
    let mut r = vec![vec![0i32; k]; n - 1];
    for row in r.iter_mut() {
        for v in row.iter_mut() {
            *v = *next;
            *next += 1;
        }
    }
    let mut added = 0;
    s.add_clause([-xs[0], r[0][0]]);
    added += 1;
    for j in 1..k {
        s.add_clause([-r[0][j]]);
        added += 1;
    }
    for i in 1..n - 1 {
        s.add_clause([-xs[i], r[i][0]]);
        s.add_clause([-r[i - 1][0], r[i][0]]);
        added += 2;
        for j in 1..k {
            s.add_clause([-xs[i], -r[i - 1][j - 1], r[i][j]]);
            s.add_clause([-r[i - 1][j], r[i][j]]);
            added += 2;
        }
        s.add_clause([-xs[i], -r[i - 1][k - 1]]);
        added += 1;
    }
    s.add_clause([-xs[n - 1], -r[n - 2][k - 1]]);
    added + 1
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let cnf_path = &args[0];
    let map_path = &args[1];
    let dmax: usize = arg_val(&args, "--dmax").unwrap_or(21);
    let seed: Option<i32> = arg_val(&args, "--seed");
    let shuffle: Option<u64> = arg_val(&args, "--shuffle");
    let lex = !args.iter().any(|a| a == "--no-lex");

    let mut solver: Solver = Solver::new();
    if let Some(sd) = seed {
        assert!(solver.set_option("seed", sd), "seed option");
        assert!(solver.set_option("phase", sd & 1), "phase option");
    }

    let txt = std::fs::read_to_string(cnf_path).expect("cnf");
    let mut nvars = 0i32;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    for line in txt.lines() {
        let line = line.trim();
        if line.starts_with('p') {
            nvars = line.split_whitespace().nth(2).unwrap().parse().unwrap();
            continue;
        }
        if line.is_empty() || line.starts_with('c') {
            continue;
        }
        let lits: Vec<i32> = line
            .split_whitespace()
            .map(|t| t.parse().unwrap())
            .take_while(|&l| l != 0)
            .collect();
        if !lits.is_empty() {
            clauses.push(lits);
        }
    }
    if let Some(mut st) = shuffle {
        st = st.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1;
        for i in (1..clauses.len()).rev() {
            st ^= st << 13;
            st ^= st >> 7;
            st ^= st << 17;
            clauses.swap(i, (st % (i as u64 + 1)) as usize);
        }
    }
    let nbase = clauses.len();
    for c in &clauses {
        solver.add_clause(c.iter().copied());
    }
    drop(clauses);

    let mut map = vec![0usize; 621];
    for line in std::fs::read_to_string(map_path).expect("map").lines() {
        let mut it = line.split_whitespace();
        if let (Some(v), Some(r)) = (it.next(), it.next()) {
            map[v.parse::<usize>().unwrap()] = r.parse().unwrap();
        }
    }
    let avar = |m: usize, k: usize| map[9 * m + k] as i32 + 1;
    for m in 0..23 {
        for k in 0..9 {
            assert_eq!(map[9 * m + k], 9 * m + k, "A-bits must be the representatives");
        }
    }
    // B_m = A_succ(m) coordinate-for-coordinate defines the cyclic action.
    let succ: Vec<usize> = (0..23)
        .map(|m| {
            let t = map[207 + 9 * m] / 9;
            for k in 0..9 {
                assert_eq!(map[207 + 9 * m + k], 9 * t + k, "unexpected map structure");
            }
            t
        })
        .collect();
    let mut orbits: Vec<[usize; 3]> = Vec::new();
    let mut fixed: Vec<usize> = Vec::new();
    let mut seen = [false; 23];
    for m in 0..23 {
        if seen[m] {
            continue;
        }
        if succ[m] == m {
            fixed.push(m);
            seen[m] = true;
        } else {
            let (m1, m2) = (succ[m], succ[succ[m]]);
            assert_eq!(succ[m2], m, "orbits must be 3-cycles");
            seen[m] = true;
            seen[m1] = true;
            seen[m2] = true;
            orbits.push([m, m1, m2]);
        }
    }

    let mut next = nvars + 1;
    let block_of = |m: usize| (0..9).map(|k| avar(m, k)).collect::<Vec<i32>>();
    let mut nlex = 0usize;
    if lex {
        for o in &orbits {
            nlex += lex_le(&mut solver, &block_of(o[0]), &block_of(o[1]), &mut next);
            nlex += lex_le(&mut solver, &block_of(o[0]), &block_of(o[2]), &mut next);
        }
        let cat = |o: &[usize; 3]| o.iter().flat_map(|&m| block_of(m)).collect::<Vec<i32>>();
        for w in orbits.windows(2) {
            nlex += lex_le(&mut solver, &cat(&w[0]), &cat(&w[1]), &mut next);
        }
        for w in fixed.windows(2) {
            nlex += lex_le(&mut solver, &block_of(w[0]), &block_of(w[1]), &mut next);
        }
    }

    let mut npin = 0usize;
    if let Some(pf) = args.iter().position(|a| a == "--pin").and_then(|i| args.get(i + 1)) {
        let pat = std::fs::read_to_string(pf).expect("pin file");
        let pat = pat.trim();
        assert_eq!(pat.len(), 207, "pin pattern needs 207 chars");
        for (p, ch) in pat.bytes().enumerate() {
            let lit = avar(p / 9, p % 9);
            match ch {
                b'1' => solver.add_clause([lit]),
                b'0' => solver.add_clause([-lit]),
                _ => continue,
            }
            npin += 1;
        }
    }

    let ybase = next - 1;
    next += 511;
    let y = |v: usize| ybase + v as i32;
    for m in 0..23 {
        for v in 1..512usize {
            let mut c: Vec<i32> = (0..9)
                .map(|k| if (v >> (8 - k)) & 1 == 1 { -avar(m, k) } else { avar(m, k) })
                .collect();
            c.push(y(v));
            solver.add_clause(c);
        }
    }
    let ys: Vec<i32> = (1..512).map(y).collect();
    let ncard = at_most(&mut solver, &ys, dmax, &mut next);
    eprintln!(
        "c symcegar: {nbase} base clauses, {} orbits + {} fixed, {nlex} lex clauses, \
         {} indicator clauses, {ncard} counter clauses (dmax {dmax}), {npin} pinned bits, \
         seed {seed:?}, shuffle {shuffle:?}",
        orbits.len(),
        fixed.len(),
        23 * 511
    );

    let stdin = std::io::stdin();
    let mut out = std::io::stdout();
    for line in stdin.lock().lines() {
        let line = line.unwrap();
        let mut it = line.split_whitespace();
        match it.next() {
            Some("solve") => {
                match it.next().and_then(|t| t.parse::<f32>().ok()) {
                    Some(secs) => solver.set_callbacks(Some(cadical::Timeout::new(secs))),
                    None => solver.set_callbacks(None),
                }
                let r = match solver.solve() {
                    Some(true) => {
                        let bits: String = (0..621)
                            .map(|v| {
                                if solver.value(map[v] as i32 + 1).unwrap_or(false) { '1' } else { '0' }
                            })
                            .collect();
                        format!("b {bits}")
                    }
                    Some(false) => "s UNSAT".to_string(),
                    None => "s UNKNOWN".to_string(),
                };
                writeln!(out, "{r}").unwrap();
            }
            Some("block") => {
                let c: Vec<i32> = it.map(|t| -y(t.parse().unwrap())).collect();
                assert!(!c.is_empty(), "empty block");
                solver.add_clause(c);
                writeln!(out, "ok").unwrap();
            }
            Some("check") => {
                let pat = it.next().expect("pattern");
                assert_eq!(pat.len(), 207, "check needs 207 chars");
                for (p, ch) in pat.bytes().enumerate() {
                    let lit = avar(p / 9, p % 9);
                    match ch {
                        b'1' => solver.assume(lit),
                        b'0' => solver.assume(-lit),
                        _ => {}
                    }
                }
                let r = match solver.solve() {
                    Some(true) => "s SAT",
                    Some(false) => "s UNSAT",
                    None => "s UNKNOWN",
                };
                writeln!(out, "{r}").unwrap();
            }
            Some("stats") => {
                writeln!(
                    out,
                    "stats conflicts={} decisions={} learned={}",
                    solver.conflicts(),
                    solver.decisions(),
                    solver.learned_clauses()
                )
                .unwrap();
            }
            Some("quit") | None => break,
            Some(other) => panic!("unknown command {other}"),
        }
        out.flush().unwrap();
    }
}
