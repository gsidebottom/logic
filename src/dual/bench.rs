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
    EffectivePathController, GreedyDynamicCoverController, GreedyMaxCoverController, Outcome, SearchMode,
    SmartDualPathController, solve_dual,
};
use crate::matrix::Matrix;
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

#[allow(dead_code)]
fn load_cnf(path: &str) -> Option<NNF> {
    let f = std::fs::File::open(path).ok()?;
    let r = std::io::BufReader::new(f);
    let (_nvars, clauses) = parse_dimacs(r).ok()?;
    Some(cnf_complement_nnf(&clauses))
}

/// Load a CNF and keep both the search-target (the complement NNF
/// the matrix-method walks) *and* the raw clauses (so the cadical
/// runner can solve the original CNF directly without round-tripping
/// through tseitin).
fn load_cnf_full(path: &str) -> Option<(NNF, Vec<Vec<i32>>)> {
    let f = std::fs::File::open(path).ok()?;
    let r = std::io::BufReader::new(f);
    let (_nvars, clauses) = parse_dimacs(r).ok()?;
    Some((cnf_complement_nnf(&clauses), clauses))
}

// ─── Faulty-adder formula loading via jq ──────────────────────────────────

/// Generate the NNF for a `faulty_add_at_most(...)` formula via jq.
/// `jq_args` is the argument string, e.g. `"3;1;1;0;3;0;1"`.  Mirrors the
/// helper used in `matrix.rs`'s ignored faulty-adder benches.
///
/// Returns the *complement* NNF (the SAT-search target).
#[allow(dead_code)]
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

/// Same as `faulty_add_at_most_nnf` but also returns the source
/// `Matrix`, so a cadical baseline can be run alongside the
/// matrix-method search.
fn faulty_add_at_most_full(jq_args: &str) -> Option<(NNF, Matrix)> {
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
    Some((matrix.nnf_complement.clone(), matrix))
}

/// Generate the NNF for a `bnc(n; w)`-based BMC formula via jq.
/// `expression` is the body that follows `expr.jq`, `math.jq`, and
/// `bmc.jq` definitions — e.g.
///   `"16 as $w | 8 as $n | prod(bnc($n;$w), br(v_gt(\"c\\($n)\"; $n; $w)))"`.
/// Returns the *complement* NNF (the SAT-search target).
#[allow(dead_code)]
fn bmc_nnf(expression: &str) -> Option<NNF> {
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
    let expr = load("expr.jq")?;
    let math = load("math.jq")?;
    let bmc  = load("bmc.jq")?;
    let combined = format!("{}\n{}\n{}\n{}", expr, math, bmc, expression);
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

/// Same as `bmc_nnf` but also returns the source `Matrix` for
/// running a cadical baseline alongside.
fn bmc_full(expression: &str) -> Option<(NNF, Matrix)> {
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
    let expr = load("expr.jq")?;
    let math = load("math.jq")?;
    let bmc  = load("bmc.jq")?;
    let combined = format!("{}\n{}\n{}\n{}", expr, math, bmc, expression);
    let loader  = PreludeLoader();
    let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
    let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();
    let iter    = run_query(&combined, context, input, &loader).ok()?;
    let json_vals: Vec<String> = iter.filter_map(|r| r.ok().map(|v| v.to_string())).collect();
    if json_vals.is_empty() { return None; }
    let formula: String = serde_json::from_str(&json_vals[0]).ok()?;
    let matrix = crate::matrix::Matrix::try_from(formula.as_str()).ok()?;
    Some((matrix.nnf_complement.clone(), matrix))
}

// ─── CaDiCaL runners ──────────────────────────────────────────────────────

/// Solve a raw CNF clause set with CaDiCaL.  Returns true iff SAT.
fn run_cadical_clauses(clauses: Vec<Vec<i32>>) -> bool {
    let mut solver: cadical::Solver = cadical::Solver::new();
    for c in &clauses { solver.add_clause(c.iter().copied()); }
    matches!(solver.solve(), Some(true))
}

/// Solve via `Matrix::cadical_satisfiable` — used for jq-loaded
/// formulas where the CNF would otherwise need to be re-derived.
fn run_cadical_matrix(matrix: Matrix) -> bool {
    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");
    rt.block_on(async move {
        let (handle, _cancel) = matrix.cadical_satisfiable();
        match handle.await {
            Ok(Ok(r))  => r.result.is_ok(),
            Ok(Err(_)) => false,
            Err(_)     => false,
        }
    })
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

// Dynamic-greedy cover controller — same shape as static Greedy but
// scores by submodular marginal gain (paths the candidate would *newly*
// cover given those already chosen).  Uses `BddBansCoverState` so the
// gain query is `cardinality(valid_bdd ∧ box(pair))`.
fn run_dual_greedydyn_basic(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, GreedyDynamicCoverController::default(),
        BasicDualPathController::<BddBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_greedydyn_smart(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, GreedyDynamicCoverController::default(),
        SmartDualPathController::<BddBansCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_greedydyn_cdcl(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, GreedyDynamicCoverController::default(),
        CdclDualPathController::<BddBansCoverState>::default(),
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

// EffectivePathController — composes CDCL inner with the
// effective-path-count layer.  Plug into Basic / Greedy A controllers.
fn run_dual_basic_effective(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, BasicCoverController::default(),
        EffectivePathController::<BasicCoverState>::default(),
        SearchMode::Satisfiable), Outcome::Sat(_))
}
fn run_dual_greedy_effective(nnf: NNF) -> bool {
    matches!(solve_dual(&nnf, GreedyMaxCoverController::default(),
        EffectivePathController::<BasicCoverState>::default(),
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

/// Bench harness driver — runs an optional CaDiCaL baseline as the
/// first row, then `matrix.{smart,cdcl}`, then the eleven `dual`
/// configurations.  The cadical closure is consumed on the first
/// (and only) attempt; pass `None` to skip the cadical row entirely.
fn bench_one_with_cadical<F>(name: &str, nnf: NNF, cadical: Option<F>)
where F: FnOnce() -> bool + Send + 'static
{
    eprintln!("\n=== {} ===", name);
    let mut answers: Vec<Option<bool>> = Vec::new();

    if let Some(cd) = cadical {
        let r = run_with_timeout(cd);
        match r {
            Some((is_sat, dt)) => {
                answers.push(Some(is_sat));
                eprintln!("{}  {:>10.3} ms   {}",
                          "cadical                  ",
                          dt.as_secs_f64() * 1000.0,
                          if is_sat { "SAT" } else { "UNSAT" });
            }
            None => {
                answers.push(None);
                eprintln!("{}     TIMEOUT (>{:.0}s)",
                          "cadical                  ",
                          PER_CONFIG_TIMEOUT.as_secs_f64());
            }
        }
    }

    type Runner = fn(NNF) -> bool;
    let configs: &[(&str, Runner)] = &[
        ("matrix.smart             ", |n| run_single(n, Backend::Smart)),
        ("matrix.cdcl              ", |n| run_single(n, Backend::Cdcl)),
        ("dual basic    × basic    ", run_dual_basic_basic),
        ("dual basic    × smart    ", run_dual_basic_smart),
        ("dual basic    × cdcl     ", run_dual_basic_cdcl),
        ("dual basic    × effective", run_dual_basic_effective),
        ("dual greedy   × basic    ", run_dual_greedy_basic),
        ("dual greedy   × smart    ", run_dual_greedy_smart),
        ("dual greedy   × cdcl     ", run_dual_greedy_cdcl),
        ("dual greedy   × effective", run_dual_greedy_effective),
        ("dual greedy⁺  × basic    ", run_dual_greedydyn_basic),
        ("dual greedy⁺  × smart    ", run_dual_greedydyn_smart),
        ("dual greedy⁺  × cdcl     ", run_dual_greedydyn_cdcl),
        ("dual cnf-bans × basic    ", run_dual_cnfbans_basic),
        ("dual cnf-bans × smart    ", run_dual_cnfbans_smart),
        ("dual cnf-bans × cdcl     ", run_dual_cnfbans_cdcl),
        ("dual bdd-bans × basic    ", run_dual_bddbans_basic),
        ("dual bdd-bans × smart    ", run_dual_bddbans_smart),
        ("dual bdd-bans × cdcl     ", run_dual_bddbans_cdcl),
    ];

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
    if let Some((nnf, clauses)) = load_cnf_full("benchmarks/php/php-10-9.cnf") {
        bench_one_with_cadical("php-10-9", nnf, Some(move || run_cadical_clauses(clauses)));
    } else {
        eprintln!("SKIP php-10-9: file not found");
    }
}

#[test]
#[ignore]
fn bench_dual_php_11_10() {
    if let Some((nnf, clauses)) = load_cnf_full("benchmarks/php/php-11-10.cnf") {
        bench_one_with_cadical("php-11-10", nnf, Some(move || run_cadical_clauses(clauses)));
    } else {
        eprintln!("SKIP php-11-10: file not found");
    }
}

#[test]
#[ignore]
fn bench_dual_php_12_11() {
    if let Some((nnf, clauses)) = load_cnf_full("benchmarks/php/php-12-11.cnf") {
        bench_one_with_cadical("php-12-11", nnf, Some(move || run_cadical_clauses(clauses)));
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
    let nnf = cnf_complement_nnf(&clauses);
    let clauses_for_cadical = clauses;
    bench_one_with_cadical("random-3sat n=30", nnf,
        Some(move || run_cadical_clauses(clauses_for_cadical)));
}

#[test]
#[ignore]
fn bench_dual_faulty_add_3bit() {
    if let Some((nnf, m)) = faulty_add_at_most_full("3;1;1;0;3;0;1") {
        bench_one_with_cadical("faulty_add_at_most(3;1;1;0;3;0;1) SAT", nnf,
            Some(move || run_cadical_matrix(m)));
    } else {
        eprintln!("SKIP faulty_add_3bit: jq libs not available");
    }
}

#[test]
#[ignore]
fn bench_dual_faulty_add_4bit() {
    if let Some((nnf, m)) = faulty_add_at_most_full("4;1;1;0;3;0;1") {
        bench_one_with_cadical("faulty_add_at_most(4;1;1;0;3;0;1) SAT", nnf,
            Some(move || run_cadical_matrix(m)));
    } else {
        eprintln!("SKIP faulty_add_4bit: jq libs not available");
    }
}

#[test]
#[ignore]
fn bench_dual_faulty_add_27bit_unsat() {
    if let Some((nnf, m)) = faulty_add_at_most_full("27;0;134217727;1;134217727;1;1") {
        bench_one_with_cadical("faulty_add_at_most(27;...;1) UNSAT", nnf,
            Some(move || run_cadical_matrix(m)));
    } else {
        eprintln!("SKIP faulty_add_27bit_unsat: jq libs not available");
    }
}

/// BMC zero-counter overflow check (UNSAT): a counter `c` initialised
/// to 0 increments for each zero-valued element of an n-array of
/// w-bit integers.  After n iterations `c` cannot exceed n, so the
/// added constraint `c_n > n` makes the formula unsatisfiable.
/// Uses w=16 / n=8 so `c` has plenty of headroom — UNSAT comes from
/// the counting semantics, not from arithmetic overflow.  We run
/// only the cdcl-side configurations because the formula is large
/// and the smart/basic B-controllers are not competitive on it.
#[test]
#[ignore]
fn bench_dual_bmc_count_zeros_n8_w16_cdcl_only() {
    let expr = "16 as $w | 8 as $n | \
                prod(bnc($n;$w), br(v_gt(\"c\\($n)\"; $n; $w)))";
    let Some((nnf, matrix)) = bmc_full(expr) else {
        eprintln!("SKIP bmc_count_zeros_n8_w16: jq libs not available");
        return;
    };
    eprintln!("\n=== bmc count-zeros n=8 w=16 + (c_n > n) UNSAT — cdcl-only ===");
    cdcl_only_with_cadical(nnf, Some(move || run_cadical_matrix(matrix)), true);
}

/// 27-bit / 2-fault SAT.  Single-DFS matrix.cdcl takes ~56s on this
/// case; we run only the four "× cdcl" configurations to stay
/// within reasonable bench time (others are slower variants).
#[test]
#[ignore]
fn bench_dual_faulty_add_27bit_sat_cdcl_only() {
    let Some((nnf, matrix)) = faulty_add_at_most_full("27;0;134217727;1;134217727;1;2") else {
        eprintln!("SKIP faulty_add_27bit_sat: jq libs not available");
        return;
    };
    eprintln!("\n=== faulty_add_at_most(27;...;2) SAT — cdcl-only ===");
    cdcl_only_with_cadical(nnf, Some(move || run_cadical_matrix(matrix)), false);
}

/// Shared cdcl-only harness used by the BMC and 27-bit-2f benches.
/// Runs cadical first (if a runner is provided), then matrix.cdcl
/// and the four `dual × cdcl` configurations.  `expect_unsat = true`
/// panics if any non-timed-out config returns SAT.
fn cdcl_only_with_cadical<F>(nnf: NNF, cadical: Option<F>, expect_unsat: bool)
where F: FnOnce() -> bool + Send + 'static
{
    let mut answers: Vec<Option<bool>> = Vec::new();
    if let Some(cd) = cadical {
        let r = run_with_timeout(cd);
        match r {
            Some((is_sat, dt)) => {
                answers.push(Some(is_sat));
                eprintln!("{}  {:>10.3} ms   {}",
                          "cadical                  ",
                          dt.as_secs_f64() * 1000.0,
                          if is_sat { "SAT" } else { "UNSAT" });
            }
            None => {
                answers.push(None);
                eprintln!("{}     TIMEOUT (>{:.0}s)",
                          "cadical                  ",
                          PER_CONFIG_TIMEOUT.as_secs_f64());
            }
        }
    }
    type Runner = fn(NNF) -> bool;
    let configs: &[(&str, Runner)] = &[
        ("matrix.cdcl              ", |n| run_single(n, Backend::Cdcl)),
        ("dual basic    × cdcl     ", run_dual_basic_cdcl),
        ("dual greedy   × cdcl     ", run_dual_greedy_cdcl),
        ("dual greedy⁺  × cdcl     ", run_dual_greedydyn_cdcl),
        ("dual cnf-bans × cdcl     ", run_dual_cnfbans_cdcl),
        ("dual bdd-bans × cdcl     ", run_dual_bddbans_cdcl),
        ("dual basic    × effective", run_dual_basic_effective),
        ("dual greedy   × effective", run_dual_greedy_effective),
    ];
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
    if expect_unsat {
        if let Some(true) = baseline {
            panic!("formula should be UNSAT but at least one config returned SAT");
        }
    }
}

/// `plus(a;b;c;w) ∧ a=max ∧ b=max ∧ c=2·max` for `w ∈ {3, 4, 5, 6}`.
/// Unique-SAT formula whose NNF is non-flat (XOR/iff expansions).
/// CaDiCaL is flat-fast (~0.3 ms regardless of `w`); the existing
/// matrix.cdcl grows ~5× per bit; this bench measures whether the
/// new `EffectivePathController` closes that gap.
#[test]
#[ignore]
fn bench_dual_plus_pinning_sweep() {
    use xq::{module_loader::PreludeLoader, run_query, Value as XqValue};
    let strip = |s: &str| -> String {
        let cut = s.find("\n# === tests ===").unwrap_or(s.len());
        let head = &s[..cut];
        let mut out = String::new();
        let mut lines = head.lines();
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
    let load = |n: &str| -> Option<String> {
        std::fs::read_to_string(format!("lib/{}", n)).ok().map(|s| strip(&s))
    };
    let Some(expr_jq) = load("expr.jq") else {
        eprintln!("SKIP plus_pinning: jq libs not available");
        return;
    };
    let Some(math_jq) = load("math.jq") else {
        eprintln!("SKIP plus_pinning: jq libs not available");
        return;
    };

    eprintln!("\n=== plus(a;b;c;w) ∧ a=max ∧ b=max ∧ c=2·max  (unique SAT)");
    eprintln!("{:>3}  {:>4}  {:>16}  {:>11}  {:>10}  {:>10}  {:>11}  {:>11}",
              "w", "vars", "complement_paths",
              "matrix.cdcl", "cadical", "basic×cdcl",
              "basic×eff", "greedy×eff");
    for w in 3..=6usize {
        let max = (1u64 << (w-1)) - 1;
        let combined = format!(
            "{}\n{}\nprod(plus(\"a\";\"b\";\"c\";{w}), \
             prod(v_eq(\"a\";{a};{w})), \
             prod(v_eq(\"b\";{a};{w})), \
             prod(v_eq(\"c\";{c};{w})))",
            expr_jq, math_jq, w=w, a=max, c=2*max);
        let loader = PreludeLoader();
        let context = std::iter::once(Ok::<XqValue, xq::InputError>(XqValue::Null));
        let input   = std::iter::empty::<Result<XqValue, xq::InputError>>();
        let json: String = run_query(&combined, context, input, &loader).unwrap()
            .next().unwrap().unwrap().to_string();
        let formula: String = serde_json::from_str(&json).unwrap();
        let m = Matrix::try_from(formula.as_str()).unwrap();
        let n_vars = m.ast.vars.len();
        let pc = m.nnf_complement.path_count();
        let nnf = m.nnf_complement.clone();
        drop(m);

        let f1 = formula.clone();
        let t_cd = run_with_timeout(move || {
            let m = Matrix::try_from(f1.as_str()).unwrap();
            run_cadical_matrix(m)
        }).map(|(_,d)| d);
        let n1 = nnf.clone();
        let t_mx  = run_with_timeout(move || run_single(n1, Backend::Cdcl)).map(|(_,d)| d);
        let n2 = nnf.clone();
        let t_bc  = run_with_timeout(move || run_dual_basic_cdcl(n2)).map(|(_,d)| d);
        let n3 = nnf.clone();
        let t_be  = run_with_timeout(move || run_dual_basic_effective(n3)).map(|(_,d)| d);
        let n4 = nnf.clone();
        let t_ge  = run_with_timeout(move || run_dual_greedy_effective(n4)).map(|(_,d)| d);

        let fmt = |t: Option<std::time::Duration>| match t {
            Some(d) => format!("{:>8.2} ms", d.as_secs_f64() * 1000.0),
            None    => format!("{:>11}", "TIMEOUT"),
        };
        eprintln!("{:>3}  {:>4}  {:>16.3e}  {}  {}  {}  {}  {}",
                  w, n_vars, pc,
                  fmt(t_mx), fmt(t_cd), fmt(t_bc), fmt(t_be), fmt(t_ge));
    }
}

/// Focused bench across a curated set of test cases against the
/// configurations that have so far survived our table-comparison
/// exercises.  As we discover faster controllers we'll add them; as
/// configurations fall behind on every row of this table we'll prune
/// them.  Currently:
///
/// * `cadical` (baseline)
/// * `matrix.smart` — single-DFS with cross-clause propagation
/// * `matrix.cdcl` — single-DFS with full CDCL learning
/// * `dual greedy × cdcl` — dual framework, static box-size cover
///   selection + CDCL B side
/// * `dual greedy × effective` — dual framework, static cover +
///   effective-path-count B side
///
/// Test cases (four rows):
/// 1. random 3-SAT n=30, 90 clauses (deterministic LCG seed) — SAT
/// 2. `faulty_add_at_most(16;0;65535;1;65535;1;1)` — UNSAT (1 fault)
/// 3. `faulty_add_at_most(16;0;65535;1;65535;1;2)` — SAT (2 faults)
/// 4. BMC count-zeros n=8 w=16 + `c_n > n` — UNSAT
///
/// 16-bit faulty-adder rows replaced the original 27-bit ones from
/// the table-fill exercise so `matrix.cdcl` / `matrix.smart` finish
/// in tractable time.  3-bit and 4-bit rows were dropped — they
/// were dominated by the 16-bit cases as a stress-test.  Skips any
/// row whose jq sources aren't available (so the test passes in CI
/// without the `lib/` directory).
#[test]
#[ignore]
fn bench_focused_top_config() {
    eprintln!("\n=== focused top-config bench ===");
    // Each timing cell is exactly 14 chars wide so headers and rows
    // line up:
    //   "{:>9.2} ms {}"  →  "  1234.56 ms s"   (9 + 4 + 1 = 14)
    //   "{:>14}"         →  "       TIMEOUT"   (14)
    // Header columns use the same width.
    let header = format!(
        "{:<48}  {:>14}  {:>14}  {:>14}  {:>14}  {:>14}",
        "case", "cadical", "matrix.smart", "matrix.cdcl",
        "greedy×cdcl", "greedy×eff",
    );
    eprintln!("{}", header);
    eprintln!("{}", "-".repeat(header.chars().count()));

    // Helper: run the five configs against `nnf` plus a cadical
    // closure, print one labeled row.  Cadical closure is consumed
    // by value so it can carry owned state (Matrix or Vec<Vec<i32>>).
    fn run_row<F>(label: &str, nnf: NNF, cadical: F)
    where F: FnOnce() -> bool + Send + 'static
    {
        let cadical_box: Box<dyn FnOnce() -> bool + Send + 'static> = Box::new(cadical);
        let t_cd = run_with_timeout(cadical_box);
        let n1 = nnf.clone();
        let t_sm = run_with_timeout(move || run_single(n1, Backend::Smart));
        let n2 = nnf.clone();
        let t_mc = run_with_timeout(move || run_single(n2, Backend::Cdcl));
        let n3 = nnf.clone();
        let t_gc = run_with_timeout(move || run_dual_greedy_cdcl(n3));
        let n4 = nnf.clone();
        let t_ge = run_with_timeout(move || run_dual_greedy_effective(n4));

        // Each cell is exactly 14 chars wide so it lines up under
        // the 14-char headers above.
        let fmt = |t: Option<(bool, std::time::Duration)>| match t {
            Some((is_sat, d)) => format!(
                "{:>9.2} ms {}",
                d.as_secs_f64() * 1000.0,
                if is_sat { "s" } else { "u" }
            ),
            None => format!("{:>14}", "TIMEOUT"),
        };
        eprintln!(
            "{:<48}  {}  {}  {}  {}  {}",
            label, fmt(t_cd), fmt(t_sm), fmt(t_mc), fmt(t_gc), fmt(t_ge),
        );
    }

    // Row 1 — random 3-SAT n=30
    {
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
        let nnf = cnf_complement_nnf(&clauses);
        let clauses_for_cadical = clauses;
        run_row("random-3sat n=30 (SAT)", nnf,
            move || run_cadical_clauses(clauses_for_cadical));
    }

    // Rows 2–3 — faulty-adder 16-bit via jq
    let faulty_rows: &[(&str, &str)] = &[
        ("faulty_add_at_most(16;0;65535;1;65535;1;1) UNSAT",
         "16;0;65535;1;65535;1;1"),
        ("faulty_add_at_most(16;0;65535;1;65535;1;2) SAT",
         "16;0;65535;1;65535;1;2"),
    ];
    for (label, args) in faulty_rows {
        match faulty_add_at_most_full(args) {
            Some((nnf, m)) => run_row(label, nnf, move || run_cadical_matrix(m)),
            None => eprintln!("{:<48}  SKIP (jq libs not available)", label),
        }
    }

    // Row 4 — BMC count-zeros n=8 w=16 + c_n > n (UNSAT)
    {
        let expr = "16 as $w | 8 as $n | \
                    prod(bnc($n;$w), br(v_gt(\"c\\($n)\"; $n; $w)))";
        match bmc_full(expr) {
            Some((nnf, m)) =>
                run_row("bmc count-zeros n=8 w=16 + (c_n>n) UNSAT",
                        nnf, move || run_cadical_matrix(m)),
            None =>
                eprintln!("{:<48}  SKIP (jq libs not available)",
                          "bmc count-zeros n=8 w=16 + (c_n>n) UNSAT"),
        }
    }
}
