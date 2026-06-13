use logic::xor_gauss::{recover_xors, solve_xor_system, XorGaussResult};

fn main() {
    let path = std::env::args().nth(1).expect("usage: xordbg <cnf>");
    let text = std::fs::read_to_string(&path).expect("read");
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut cur: Vec<i32> = Vec::new();
    let mut nvars = 0usize;
    for line in text.lines() {
        let t = line.split_whitespace().collect::<Vec<_>>();
        if t.is_empty() || t[0] == "p" || t[0] == "c" || t[0] == "%" {
            continue;
        }
        for tok in t {
            let v: i32 = tok.parse().expect("lit");
            if v == 0 {
                if !cur.is_empty() {
                    clauses.push(std::mem::take(&mut cur));
                }
            } else {
                nvars = nvars.max(v.unsigned_abs() as usize);
                cur.push(v);
            }
        }
    }
    println!("parsed {} clauses, {} vars", clauses.len(), nvars);
    let (xors, _consumed) = recover_xors(&clauses);
    println!("recover_xors: {} XOR(s)", xors.len());
    use std::collections::BTreeMap;
    let mut by_k: BTreeMap<usize, usize> = BTreeMap::new();
    for x in &xors {
        *by_k.entry(x.vars.len()).or_default() += 1;
    }
    println!("  arity histogram: {:?}", by_k);
    for x in xors.iter().take(8) {
        println!("  sample: vars={:?} rhs={}", &x.vars[..x.vars.len().min(6)], x.rhs);
    }
    match solve_xor_system(nvars, &clauses, u64::MAX) {
        XorGaussResult::Unsat { by_bcp } => println!("solve_xor_system: UNSAT (by_bcp={})", by_bcp),
        XorGaussResult::Sat(_) => println!("solve_xor_system: SAT"),
        XorGaussResult::Simplified { recovered, forced_count, .. } =>
            println!("solve_xor_system: Simplified recovered={} forced={}", recovered, forced_count),
        XorGaussResult::Indeterminate { recovered, consumed, total } =>
            println!("solve_xor_system: Indeterminate recovered={} consumed={} total={}", recovered, consumed, total),
    }
}
