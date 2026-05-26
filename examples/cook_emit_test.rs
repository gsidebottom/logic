//! Integration test for `logic::cook_pbp`: emit a Cook PHP-4-3 proof
//! to a temp file and print the path.  Verify externally with
//! `veripb --cnf cnf.opb proof.pbp`.
//!
//! Usage: `cargo run --example cook_emit_test`

use std::io::Write;

fn main() {
    let n = 4;
    let m = 3;
    let var = |i: usize, j: usize| -> i32 { ((i - 1) * m + j) as i32 };
    let mut cs: Vec<Vec<i32>> = Vec::new();
    for i in 1..=n { cs.push((1..=m).map(|j| var(i, j)).collect()); }
    for k in 1..=m {
        for i in 1..=n {
            for j in (i + 1)..=n { cs.push(vec![-var(i, k), -var(j, k)]); }
        }
    }
    let nvars = n * m;
    let shape = logic::cook_pbp::detect_shape(&cs, nvars);
    eprintln!("detected: {}", shape.describe());

    let cnf_path = "/tmp/cook_example_php_4_3.cnf";
    let pbp_path = "/tmp/cook_example_php_4_3.pbp";
    let mut f = std::fs::File::create(cnf_path).unwrap();
    writeln!(f, "p cnf {} {}", nvars, cs.len()).unwrap();
    for c in &cs {
        for l in c { write!(f, "{} ", l).unwrap(); }
        writeln!(f, "0").unwrap();
    }
    let mut pf = std::fs::File::create(pbp_path).unwrap();
    logic::cook_pbp::emit_proof(&shape, cs.len(), &mut pf).unwrap();
    eprintln!("CNF:  {}", cnf_path);
    eprintln!("PBP:  {}", pbp_path);
    eprintln!("verify: veripb --cnf {} {}", cnf_path, pbp_path);
}
