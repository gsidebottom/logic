//! Cross-configuration benchmarks for the dual search framework.
//!
//! Compares the existing single-DFS `Matrix::satisfiable`-style
//! search (via `NNF::classify_paths_uncovered_only`) against
//! `solve_dual` with all six (A, B) controller combinations.
//!
//! Each configuration is run on a separate thread with a 60-second
//! per-config timeout.  Configurations that don't finish in time
//! are reported as `TIMEOUT` and the harness moves on to the next.
//!
//! All tests are `#[ignore]`'d.  Run with:
//!
//! ```text
//! cargo test --release --lib dual::bench:: -- --ignored --nocapture
//! ```

#![cfg(test)]

use std::io::BufRead;
use std::sync::mpsc;
use std::time::{Duration, Instant};

use crate::controller::{CdclController, SmartController};
use crate::dual::{
    BasicCoverController, BasicCoverState, BasicDualPathController, BddBansCoverController,
    BddBansCoverState, CdclDualPathController, CnfBansCoverController, CnfBansCoverState,
    GreedyMaxCoverController, Outcome, SearchMode, SmartDualPathController, solve_dual,
};
use crate::matrix::{Lit, NNF, PathParams, PathsClass, Var};

const PER_CONFIG_TIMEOUT: Duration = Duration::from_secs(60);

// ─── DIMACS parsing ───────────────────────────────────────────────────────

fn parse_dimacs<R: BufRead>(r: R) -> Result<(usize, Vec<Vec<i32>>), String> {
    let mut nvars: usize = 0;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut current: Vec<i32> = Vec::new();
    for line in r.lines() {
        let line = line.map_err(|e| e.to_string())?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') || trimmed.starts_with('%') { continue; }
        if trimmed.starts_with('p') {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() >= 3 && parts[1] == "cnf" {
                nvars = parts[2].parse().unwrap_or(0);
            }
            continue;
        }
        for tok in trimmed.split_whitespace() {
            let n: i32 = tok.parse().map_err(|_| format!("bad token {:?}", tok))?;
            if n == 0 { clauses.push(std::mem::take(&mut current)); }
            else {
                let abs = n.unsigned_abs() as usize;
                if abs > nvars { nvars = abs; }
                current.push(n);
            }
        }
    }
    if !current.is_empty() { clauses.push(current); }
    Ok((nvars, clauses))
}

fn cnf_complement_nnf(clauses: &[Vec<i32>]) -> NNF {
    if clauses.is_empty() { return NNF::Sum(vec![]); }
    let cubes: Vec<NNF> = clauses.iter().map(|cl| {
        if cl.is_empty() { return NNF::Prod(vec![]); }
        let lits: Vec<NNF> = cl.iter().map(|&n| {
            let var: Var = (n.unsigned_abs() - 1) as Var;
            // CNF lit `n` positive when n > 0; complement flips, so cube
            // lits set `neg = (n > 0)`.
            let neg = n > 0;
            NNF::Lit(Lit { var, neg })
        }).collect();
        if lits.len() == 1 { lits.into_iter().next().unwrap() } else { NNF::Prod(lits) }
    }).collect();
    NNF::Sum(cubes)
}

fn load_cnf(path: &str) -> Option<NNF> {
    let f = std::fs::File::open(path).ok()?;
    let r = std::io::BufReader::new(f);
    let (_nvars, clauses) = parse_dimacs(r).ok()?;
    Some(cnf_complement_nnf(&clauses))
}

// ─── Faulty-adder formula loading via jq ──────────────────────────────────

/// Generate the NNF for a `faulty_add_at_most(...)` formula via jq.
/// `jq_args` is the argument string, e.g. `"3;1;1;0;3;0;1"`.  Mirrors the
/// helper used in `matrix.rs`'s ignored faulty-adder benches.
///
/// Returns the *complement* NNF (the SAT-search target).
fn faulty_add_at_most_nnf(jq_args: &str) -> Option<NNF> {
    use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};
    let strip_sections = |s: &str| -> String {
        let cut = s.find("\n# === tests ===").unwrap_or(s.len());
        let head = &s[..cut];
        let mut out = String::new();
        let mut lines = head.lines();
        let peek: Vec<&str> = lines.clone().take_while(|l| l.trim().is_empty()).collect();
        for _ in 0..peek.len() { lines.next(); }
        let mut rest = lines.clone();
        if let Some(first) = rest.next() {
            if first.trim_end() == "# === deps ===" {
                lines.next();
                while let Some(l) = lines.next() {
                    if l.trim_end() == "# === end deps ===" { break; }
                }
            }
        }
        for l in lines { out.push_str(l); out.push('\n'); }
        out
    };
    let load = |name: &str| -> Option<String> {
        std::fs::read_to_string(format!("lib/{}", name)).ok().map(|s| strip_sections(&s))
    };
    let expr    = load("expr.jq")?;
    let math    = load("math.jq")?;
    let at_most = load("at_most.jq")?;
    let adder   = load("adder.jq")?;
    let combined = format!("{}\n{}\n{}\n{}\nfaulty_add_at_most({})",
                           expr, math, at_most, adder, jq_args);
    let loader  = PreludeLoader();
    let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
    let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();
    let iter    = run_query(&combined, context, input, &loader).ok()?;
    let json_vals: Vec<String> = iter.filter_map(|r| r.ok().map(|v| v.to_string())).collect();
    if json_vals.is_empty() { return None; }
    let formula: String = serde_json::from_str(&json_vals[0]).ok()?;
    let matrix = crate::matrix::Matrix::try_from(formula.as_str()).ok()?;
    Some(matrix.nnf_complement.clone())
}

// ─── Single-DFS baseline (existing Matrix::satisfiable equivalent) ────────

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Backend { Smart, Cdcl }

fn run_single(nnf: NNF, backend: Backend) -> bool {
    let params = Some(PathParams {
        uncovered_path_limit: 1,
        paths_class_limit:    usize::MAX,
        covered_prefix_limit: usize::MAX,
        no_cover:             true,
    });
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .thread_stack_size(256 * 1024 * 1024)
        .build()
        .expect("tokio runtime");
    let nnf_for_match = nnf.clone();
    rt.block_on(async move {
        let (handle, mut rx, cancel) = match backend {
            Backend::Smart => nnf.classify_paths_uncovered_only(64, move |tx| {
                SmartController::for_nnf(&nnf_for_match, params, Box::new(move |class, hl|
                    tx.blocking_send((class, hl)).is_ok())
                    as Box<dyn FnMut(PathsClass, bool) -> bool + Send>)
            }),
            Backend::Cdcl => nnf.classify_paths_uncovered_only(64, move |tx| {
                CdclController::for_nnf(&nnf_for_match, params, Box::new(move |class, hl|
                    tx.blocking_send((class, hl)).is_ok())
                    as Box<dyn FnMut(PathsClass, bool) -> bool + Send>)
            }),
        };
        let mut found = false;
        while let Some((class, _hl)) = rx.recv().await {
            if matches!(class, PathsClass::Uncovered(_)) { found = true; break; }
        }
        cancel.cancel();
        drop(rx);
        let _ = handle.await;
        found
    })
}

// ─── Dual configuration runners ───────────────────────────────────────────

fn run_dual_basic_basic(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, BasicCoverController::default(),
        BasicDualPathController::<BasicCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_basic_smart(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, BasicCoverController::default(),
        SmartDualPathController::<BasicCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_basic_cdcl(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, BasicCoverController::default(),
        CdclDualPathController::<BasicCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_greedy_basic(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, GreedyMaxCoverController::default(),
        BasicDualPathController::<BasicCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_greedy_smart(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, GreedyMaxCoverController::default(),
        SmartDualPathController::<BasicCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_greedy_cdcl(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, GreedyMaxCoverController::default(),
        CdclDualPathController::<BasicCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}

// CnfBans cover controller: A's CaDiCaL completeness check is in
// play.  Each (A, B) combination here uses CnfBansCoverState, which
// indexes triggers the same way BasicCoverState does *and* runs an
// incremental CaDiCaL solver for the bans CNF.
fn run_dual_cnfbans_basic(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, CnfBansCoverController::default(),
        BasicDualPathController::<CnfBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_cnfbans_smart(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, CnfBansCoverController::default(),
        SmartDualPathController::<CnfBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_cnfbans_cdcl(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, CnfBansCoverController::default(),
        CdclDualPathController::<CnfBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}

// BddBans cover controller: A's BDD completeness check.
fn run_dual_bddbans_basic(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, BddBansCoverController::default(),
        BasicDualPathController::<BddBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_bddbans_smart(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, BddBansCoverController::default(),
        SmartDualPathController::<BddBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_bddbans_cdcl(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, BddBansCoverController::default(),
        CdclDualPathController::<BddBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}

// ─── Timeout-bounded runner ───────────────────────────────────────────────

/// Spawn `f` on a fresh thread and wait up to `PER_CONFIG_TIMEOUT`.
/// Returns `Some((result, elapsed))` on success or `None` on timeout.
/// Note: timed-out threads continue running until they exit on their
/// own — fine for benches, since the test process is short-lived.
fn run_with_timeout(f: impl FnOnce() -> bool + Send + 'static)
    -> Option<(bool, Duration)>
{
    let (tx, rx) = mpsc::channel::<(bool, Duration)>();
    std::thread::spawn(move || {
        let start = Instant::now();
        let r = f();
        let _ = tx.send((r, start.elapsed()));
    });
    rx.recv_timeout(PER_CONFIG_TIMEOUT).ok()
}

// ─── The harness ──────────────────────────────────────────────────────────

fn bench_one(name: &str, nnf: NNF) {
    eprintln!("\n=== {} ===", name);
    type Runner = fn(NNF) -> bool;
    let configs: &[(&str, Runner)] = &[
        ("matrix.smart             ", |n| run_single(n, Backend::Smart)),
        ("matrix.cdcl              ", |n| run_single(n, Backend::Cdcl)),
        ("dual basic    × basic    ", run_dual_basic_basic),
        ("dual basic    × smart    ", run_dual_basic_smart),
        ("dual basic    × cdcl     ", run_dual_basic_cdcl),
        ("dual greedy   × basic    ", run_dual_greedy_basic),
        ("dual greedy   × smart    ", run_dual_greedy_smart),
        ("dual greedy   × cdcl     ", run_dual_greedy_cdcl),
        ("dual cnf-bans × basic    ", run_dual_cnfbans_basic),
        ("dual cnf-bans × smart    ", run_dual_cnfbans_smart),
        ("dual cnf-bans × cdcl     ", run_dual_cnfbans_cdcl),
        ("dual bdd-bans × basic    ", run_dual_bddbans_basic),
        ("dual bdd-bans × smart    ", run_dual_bddbans_smart),
        ("dual bdd-bans × cdcl     ", run_dual_bddbans_cdcl),
    ];

    let mut answers: Vec<Option<bool>> = Vec::with_capacity(configs.len());
    for (label, runner) in configs {
        let nnf_clone = nnf.clone();
        let r = run_with_timeout(move || runner(nnf_clone));
        match r {
            Some((is_sat, dt)) => {
                answers.push(Some(is_sat));
                eprintln!("{}  {:>10.3} ms   {}",
                          label, dt.as_secs_f64() * 1000.0,
                          if is_sat { "SAT" } else { "UNSAT" });
            }
            None => {
                answers.push(None);
                eprintln!("{}     TIMEOUT (>{:.0}s)",
                          label, PER_CONFIG_TIMEOUT.as_secs_f64());
            }
        }
    }
    // Sanity: every (non-timed-out) configuration should agree.
    let mut baseline: Option<bool> = None;
    for a in &answers {
        if let Some(v) = a {
            match baseline {
                None    => baseline = Some(*v),
                Some(b) => assert_eq!(*v, b,
                    "configurations disagree on {}: {:?}", name, answers),
            }
        }
    }
}

// ─── Tests ────────────────────────────────────────────────────────────────

#[test]
#[ignore]
fn bench_dual_php_10_9() {
    if let Some(nnf) = load_cnf("benchmarks/php/php-10-9.cnf") {
        bench_one("php-10-9", nnf);
    } else {
        eprintln!("SKIP php-10-9: file not found");
    }
}

#[test]
#[ignore]
fn bench_dual_php_11_10() {
    if let Some(nnf) = load_cnf("benchmarks/php/php-11-10.cnf") {
        bench_one("php-11-10", nnf);
    } else {
        eprintln!("SKIP php-11-10: file not found");
    }
}

#[test]
#[ignore]
fn bench_dual_php_12_11() {
    if let Some(nnf) = load_cnf("benchmarks/php/php-12-11.cnf") {
        bench_one("php-12-11", nnf);
    } else {
        eprintln!("SKIP php-12-11: file not found");
    }
}

#[test]
#[ignore]
fn bench_dual_random_3sat_n30() {
    fn lcg(s: &mut u64) -> u64 {
        *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *s
    }
    let n_vars = 30; let n_clauses = 90;
    let mut s = 42u64;
    let clauses: Vec<Vec<i32>> = (0..n_clauses).map(|_| {
        let mut chosen: Vec<i32> = Vec::with_capacity(3);
        while chosen.len() < 3 {
            let v = (lcg(&mut s) % (n_vars as u64)) as i32 + 1;
            if !chosen.iter().any(|&c| c.abs() == v) {
                let sign = if lcg(&mut s) & 1 == 0 { 1 } else { -1 };
                chosen.push(v * sign);
            }
        }
        chosen
    }).collect();
    bench_one("random-3sat n=30", cnf_complement_nnf(&clauses));
}

#[test]
#[ignore]
fn bench_dual_faulty_add_3bit() {
    if let Some(nnf) = faulty_add_at_most_nnf("3;1;1;0;3;0;1") {
        bench_one("faulty_add_at_most(3;1;1;0;3;0;1) SAT", nnf);
    } else {
        eprintln!("SKIP faulty_add_3bit: jq libs not available");
    }
}

#[test]
#[ignore]
fn bench_dual_faulty_add_4bit() {
    if let Some(nnf) = faulty_add_at_most_nnf("4;1;1;0;3;0;1") {
        bench_one("faulty_add_at_most(4;1;1;0;3;0;1) SAT", nnf);
    } else {
        eprintln!("SKIP faulty_add_4bit: jq libs not available");
    }
}

#[test]
#[ignore]
fn bench_dual_faulty_add_27bit_unsat() {
    if let Some(nnf) = faulty_add_at_most_nnf("27;0;134217727;1;134217727;1;1") {
        bench_one("faulty_add_at_most(27;...;1) UNSAT", nnf);
    } else {
        eprintln!("SKIP faulty_add_27bit_unsat: jq libs not available");
    }
}

/// 27-bit / 2-fault SAT.  Single-DFS matrix.cdcl takes ~56s on this
/// case; we run only the four "× cdcl" configurations to stay
/// within reasonable bench time (others are slower variants).
#[test]
#[ignore]
fn bench_dual_faulty_add_27bit_sat_cdcl_only() {
    let Some(nnf) = faulty_add_at_most_nnf("27;0;134217727;1;134217727;1;2") else {
        eprintln!("SKIP faulty_add_27bit_sat: jq libs not available");
        return;
    };
    eprintln!("\n=== faulty_add_at_most(27;...;2) SAT — cdcl-only ===");
    type Runner = fn(NNF) -> bool;
    let configs: &[(&str, Runner)] = &[
        ("matrix.cdcl              ", |n| run_single(n, Backend::Cdcl)),
        ("dual basic    × cdcl     ", run_dual_basic_cdcl),
        ("dual greedy   × cdcl     ", run_dual_greedy_cdcl),
        ("dual cnf-bans × cdcl     ", run_dual_cnfbans_cdcl),
        ("dual bdd-bans × cdcl     ", run_dual_bddbans_cdcl),
    ];
    let mut answers: Vec<Option<bool>> = Vec::with_capacity(configs.len());
    for (label, runner) in configs {
        let nnf_clone = nnf.clone();
        let r = run_with_timeout(move || runner(nnf_clone));
        match r {
            Some((is_sat, dt)) => {
                answers.push(Some(is_sat));
                eprintln!("{}  {:>10.3} ms   {}",
                          label, dt.as_secs_f64() * 1000.0,
                          if is_sat { "SAT" } else { "UNSAT" });
            }
            None => {
                answers.push(None);
                eprintln!("{}     TIMEOUT (>{:.0}s)",
                          label, PER_CONFIG_TIMEOUT.as_secs_f64());
            }
        }
    }
    let mut baseline: Option<bool> = None;
    for a in &answers {
        if let Some(v) = a {
            match baseline {
                None    => baseline = Some(*v),
                Some(b) => assert_eq!(*v, b,
                    "configurations disagree: {:?}", answers),
            }
        }
    }
}
