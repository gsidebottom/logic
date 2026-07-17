//! exactw — exact shortest-SLP solver for small resynthesis windows
//! (task #31). Instance: m inputs (unit vectors), r integer target
//! vectors (window-scaled by `scale`), find an SLP of binary ops
//! w = a*x + b*y with a,b in {±1, ±2, ±4} whose wires cover every
//! target up to ±2^e (e in -4..=4), at total cost <= budget, cost =
//! 1 per op + 1 per non-unit |coef| + 1 per output whose true
//! coefficient 2^e/scale != ±1. Iterative deepening from a span/
//! proportionality lower bound; exact within this move menu.
//! Usage: exactw inst.txt [secs]   (writes inst.sol on improvement)
use std::time::Instant;

const COEFS: [i64; 6] = [1, -1, 2, -2, 4, -4];
const EMIN: i32 = -4;
const EMAX: i32 = 4;

#[derive(Clone)]
struct Inst {
    m: usize,
    targets: Vec<Vec<i64>>,
    budget: i64,
    scale: i64,
}

fn read_inst(path: &str) -> Inst {
    let txt = std::fs::read_to_string(path).expect("inst");
    let mut it = txt.split_whitespace().map(|x| x.parse::<i64>().unwrap());
    let m = it.next().unwrap() as usize;
    let r = it.next().unwrap() as usize;
    let budget = it.next().unwrap();
    let scale = it.next().unwrap();
    let mut targets = Vec::with_capacity(r);
    for _ in 0..r {
        targets.push((0..m).map(|_| it.next().unwrap()).collect());
    }
    Inst { m, targets, budget, scale }
}

/// match target against wire: t == sgn * 2^e * w. Returns
/// (cost, e, sgn); cost = 1 unless the true coefficient magnitude
/// 2^e/scale is 1 (sign is free — folds into the output line).
fn match_cost(t: &[i64], w: &[i64], scale: i64) -> Option<(i32, i32, i64)> {
    for e in EMIN..=EMAX {
        for &sgn in &[1i64, -1] {
            let (tm, wm) = if e >= 0 { (1i64, 1i64 << e) } else { (1i64 << (-e), 1) };
            let mut ok = true;
            for i in 0..t.len() {
                if t[i] * tm != sgn * w[i] * wm {
                    ok = false;
                    break;
                }
            }
            if ok {
                let unit = e >= 0 && (1i64 << e) == scale;
                return Some((if unit { 0 } else { 1 }, e, sgn));
            }
        }
    }
    None
}

/// rank over Q of a set of integer vectors (fraction-free elimination)
fn rank_of(vs: &[Vec<i64>]) -> usize {
    let mut m: Vec<Vec<i128>> = vs
        .iter()
        .map(|v| v.iter().map(|&x| x as i128).collect())
        .collect();
    let cols = if m.is_empty() { 0 } else { m[0].len() };
    let mut rank = 0;
    for c in 0..cols {
        if let Some(p) = (rank..m.len()).find(|&i| m[i][c] != 0) {
            m.swap(rank, p);
            for i in 0..m.len() {
                if i != rank && m[i][c] != 0 {
                    let (a, b) = (m[rank][c], m[i][c]);
                    for j in 0..cols {
                        m[i][j] = m[i][j] * a - m[rank][j] * b;
                    }
                }
            }
            rank += 1;
        }
    }
    rank
}

/// lower bound in OPS: max(span deficit, unmatched proportionality classes)
fn lower_bound(wires: &[Vec<i64>], inst: &Inst) -> i64 {
    let unsat: Vec<&Vec<i64>> = inst
        .targets
        .iter()
        .filter(|t| !wires.iter().any(|w| match_cost(t, w, inst.scale).is_some()))
        .collect();
    if unsat.is_empty() {
        return 0;
    }
    // proportionality classes among unsatisfied targets
    let mut classes: Vec<&Vec<i64>> = Vec::new();
    for t in &unsat {
        if !classes.iter().any(|c| match_cost(t, c, 1).is_some()) {
            classes.push(t);
        }
    }
    let lb2 = classes.len() as i64;
    // span deficit
    let base = rank_of(&wires.to_vec());
    let mut all: Vec<Vec<i64>> = wires.to_vec();
    for t in &inst.targets {
        all.push((*t).clone());
    }
    let lb1 = (rank_of(&all) - base) as i64;
    lb1.max(lb2)
}

struct Search {
    inst: Inst,
    deadline: Instant,
    best: Option<(Vec<(i64, usize, i64, usize)>, i64)>,
    timed_out: bool,
}

impl Search {
    fn dfs(
        &mut self,
        wires: &mut Vec<Vec<i64>>,
        ops: &mut Vec<(i64, usize, i64, usize)>,
        spent: i64,
        cap: i64,
    ) -> bool {
        if Instant::now() >= self.deadline {
            self.timed_out = true;
            return false;
        }
        let lb = lower_bound(wires, &self.inst);
        if spent + lb > cap {
            return false;
        }
        if lb == 0 {
            // all targets matched; add match costs
            let mut total = spent;
            for t in &self.inst.targets {
                let mc = wires
                    .iter()
                    .filter_map(|w| match_cost(t, w, self.inst.scale))
                    .map(|(c, _, _)| c as i64)
                    .min()
                    .unwrap();
                total += mc;
            }
            if total <= cap {
                self.best = Some((ops.clone(), total));
                return true;
            }
            return false;
        }
        let n = wires.len();
        for i in 0..n {
            for j in (i + 1)..n {
                for &a in &COEFS {
                    for &b in &COEFS {
                        let mut w: Vec<i64> = (0..self.inst.m)
                            .map(|k| a * wires[i][k] + b * wires[j][k])
                            .collect();
                        if w.iter().all(|&x| x == 0) {
                            continue;
                        }
                        if wires.iter().any(|v| {
                            v == &w || v.iter().zip(&w).all(|(x, y)| *x == -*y)
                        }) {
                            continue;
                        }
                        let opcost = 1
                            + (a.abs() != 1) as i64
                            + (b.abs() != 1) as i64;
                        if spent + opcost > cap {
                            continue;
                        }
                        wires.push(w);
                        ops.push((a, i, b, j));
                        if self.dfs(wires, ops, spent + opcost, cap) {
                            return true;
                        }
                        ops.pop();
                        wires.pop();
                        if self.timed_out {
                            return false;
                        }
                    }
                }
            }
        }
        false
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let inst = read_inst(&args[1]);
    let secs: u64 = args.get(2).and_then(|x| x.parse().ok()).unwrap_or(20);
    let mut wires: Vec<Vec<i64>> = (0..inst.m)
        .map(|i| (0..inst.m).map(|j| (i == j) as i64).collect())
        .collect();
    let lb0 = lower_bound(&wires, &inst);
    if lb0 > inst.budget {
        println!("UNSAT lb {lb0} > budget {}", inst.budget);
        return;
    }
    let mut search = Search {
        inst: inst.clone(),
        deadline: Instant::now() + std::time::Duration::from_secs(secs),
        best: None,
        timed_out: false,
    };
    for cap in lb0..=inst.budget {
        let mut ops = Vec::new();
        if search.dfs(&mut wires, &mut ops, 0, cap) {
            break;
        }
        if search.timed_out {
            println!("TIMEOUT at cap {cap} (budget {})", inst.budget);
            return;
        }
    }
    match search.best {
        Some((ops, total)) => {
            let sol = args[1].replace(".txt", ".sol");
            let mut out = String::new();
            let mut wires: Vec<Vec<i64>> = (0..inst.m)
                .map(|i| (0..inst.m).map(|j| (i == j) as i64).collect())
                .collect();
            for &(a, i, b, j) in &ops {
                out.push_str(&format!("{a} {i} {b} {j}\n"));
                let w: Vec<i64> = (0..inst.m)
                    .map(|k| a * wires[i][k] + b * wires[j][k])
                    .collect();
                wires.push(w);
            }
            for (t_idx, t) in inst.targets.iter().enumerate() {
                let (w_idx, e, sgn) = wires
                    .iter()
                    .enumerate()
                    .filter_map(|(wi, w)| {
                        match_cost(t, w, inst.scale).map(|(_, e, s)| (wi, e, s))
                    })
                    .next()
                    .expect("matched target lost");
                out.push_str(&format!("match {t_idx} {w_idx} {e} {sgn}\n"));
            }
            std::fs::write(&sol, out).unwrap();
            println!("IMPROVED cost {total} (budget {}) -> {sol}", inst.budget);
        }
        None => println!("OPTIMAL-AT-BUDGET none <= {}", inst.budget),
    }
}
