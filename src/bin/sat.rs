//! `sat` — a DIMACS-CNF SAT solver driven by the matrix-method search with
//! [`SmartController`](logic::controller::SmartController).
//!
//! Reads a problem in DIMACS CNF on stdin, prints the result on stdout in
//! the SAT-competition output format:
//!
//! ```text
//! s SATISFIABLE
//! v 1 -2 3 -4 5 0
//! ```
//!
//! or
//!
//! ```text
//! s UNSATISFIABLE
//! ```
//!
//! Anything not on `s`/`v` lines (status, parse counts, etc.) goes to stderr
//! prefixed with `c ` so it's a valid DIMACS comment line if redirected.
//!
//! ## Usage
//!
//! ```sh
//! cargo run --release --bin sat < problem.cnf
//! cat problem.cnf | cargo run --release --bin sat
//! cargo run --release --bin sat -- --progress < problem.cnf
//! ```
//!
//! ## Flags
//!
//! - `--progress` / `-p` — render a live progress bar to stderr while
//!   the search runs (only when stderr is a TTY; ignored otherwise so
//!   piped output stays clean).  Press `Ctrl-C` to interrupt; the
//!   terminal cursor and line state are restored on exit.
//!
//! ## Approach
//!
//! The search is the same one `Matrix::satisfiable` uses: we build the NNF
//! of the formula's *complement* (a Sum-of-Prods, by De Morgan applied to
//! each clause) and look for a non-complementary path through it.  Path
//! literals — negated — give a satisfying assignment for the original CNF.
//!
//! The DFS is driven by a [`SmartController`] preprocessed for the
//! complement, so every Prod-of-`Lit`s "clause complement" gets watch-lists
//! enabling cross-clause unit propagation.  This is dramatically faster
//! than the cover-aware controller on structured inputs (adders, encoders,
//! at-most-N constraints — see `bench_faulty_add_at_most`).
//!
//! For UNSAT problems we'll exhaustively explore the search tree, which is
//! the same asymptotic cost as a brute DPLL.  CaDiCaL would be faster
//! there; this binary is mainly useful for prototyping the matrix-side
//! solver and for inputs where the SmartController's propagation-driven
//! search wins.

use std::collections::HashSet;
use std::io::{self, BufRead, IsTerminal, Write};
use std::time::{Duration, Instant};

use logic::matrix::{
    Lit, NNF, PathClassificationHandle, PathParams, PathsClass, Var,
    smart_controller_builder,
};

// ─── DIMACS parser ─────────────────────────────────────────────────────────

/// Parse a DIMACS CNF stream into `(num_vars, clauses)`.
///
/// The format is permissive: comments (`c ...`), the optional problem line
/// (`p cnf <vars> <clauses>`), and clauses as space-separated nonzero
/// integers terminated by `0`.  Whitespace (including newlines) inside a
/// clause is ignored, so a clause may span multiple lines.  Trailing
/// content with no terminating `0` is silently included as a final clause.
fn parse_dimacs<R: BufRead>(r: R) -> Result<(usize, Vec<Vec<i32>>), String> {
    let mut nvars: usize = 0;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut current: Vec<i32> = Vec::new();

    for (lineno, line) in r.lines().enumerate() {
        let line = line.map_err(|e| format!("read error at line {}: {}", lineno + 1, e))?;
        let trimmed = line.trim();
        if trimmed.is_empty() || trimmed.starts_with('c') || trimmed.starts_with('%') {
            continue;
        }
        if trimmed.starts_with('p') {
            let parts: Vec<&str> = trimmed.split_whitespace().collect();
            if parts.len() < 4 || parts[1] != "cnf" {
                return Err(format!(
                    "malformed problem line at line {}: {:?}", lineno + 1, trimmed));
            }
            nvars = parts[2].parse()
                .map_err(|e| format!("bad variable count {:?}: {}", parts[2], e))?;
            continue;
        }
        for tok in trimmed.split_whitespace() {
            let n: i32 = tok.parse().map_err(|e|
                format!("bad token {:?} at line {}: {}", tok, lineno + 1, e))?;
            if n == 0 {
                clauses.push(std::mem::take(&mut current));
            } else {
                let abs = n.unsigned_abs() as usize;
                if abs > nvars { nvars = abs; }
                current.push(n);
            }
        }
    }
    if !current.is_empty() {
        clauses.push(current);
    }
    Ok((nvars, clauses))
}

// ─── CNF → complement NNF ─────────────────────────────────────────────────

/// Build the NNF of the *complement* of the given CNF clause set.
///
/// By De Morgan, `¬(C₁ ∧ C₂ ∧ …) = (¬C₁) ∨ (¬C₂) ∨ …` and
/// `¬(l₁ ∨ l₂ ∨ …) = (¬l₁ ∧ ¬l₂ ∧ …)`, so every clause
/// `(l₁ ∨ l₂ ∨ … ∨ lₖ)` becomes a "cube" `(¬l₁ ∧ ¬l₂ ∧ … ∧ ¬lₖ)` and the
/// whole formula becomes a Sum of those cubes.  The matrix-method search
/// treats this exactly: each `Sum` child is one clause-complement, and the
/// `SmartController` indexes the constituent `Prod`-of-`Lit`s for unit
/// propagation.
fn cnf_complement_nnf(clauses: &[Vec<i32>]) -> NNF {
    if clauses.is_empty() {
        // Empty CNF is trivially true; its complement is false (empty Sum).
        return NNF::Sum(vec![]);
    }
    let cubes: Vec<NNF> = clauses.iter().map(|cl| {
        if cl.is_empty() {
            // Empty clause is false (the empty disjunction); its
            // complement is true (the empty conjunction).  Caller has
            // already short-circuited UNSAT in this case, but include for
            // completeness.
            NNF::Prod(vec![])
        } else {
            let lits: Vec<NNF> = cl.iter().map(|&n| {
                let var: Var = (n.unsigned_abs() - 1) as Var;
                let neg = n > 0;     // negate every lit going from clause → its negation
                NNF::Lit(Lit { var, neg })
            }).collect();
            // Single-literal clause → a "cube" of one lit collapses to that lit.
            if lits.len() == 1 { lits.into_iter().next().unwrap() } else { NNF::Prod(lits) }
        }
    }).collect();
    if cubes.len() == 1 { cubes.into_iter().next().unwrap() } else { NNF::Sum(cubes) }
}

// ─── Solver entry ─────────────────────────────────────────────────────────

/// Outcome of the search: a satisfying assignment, an exhausted search
/// (UNSAT), or an interruption (Ctrl-C before either of the above
/// resolved).  The assignment is stored 0-indexed: `asgn[i]` is the
/// truth value of variable `i + 1` in DIMACS numbering.
enum SearchOutcome {
    Sat(Vec<bool>),
    Unsat,
    Interrupted,
}

/// Convert a path's literal-set (drawn from the complement NNF) into a
/// satisfying assignment for the original CNF.  Each path lit `l`,
/// negated, contributes `asgn[l.var] = l.neg`.  Variables not on the
/// path default to `true` (free choice — keeps the output a complete
/// assignment, which DIMACS checkers expect).
fn path_lits_to_assignment(nvars: usize, path_lits: &[&Lit]) -> Vec<bool> {
    let mut seen = HashSet::new();
    let mut asgn = vec![true; nvars];
    for l in path_lits {
        if !seen.insert(l.var) { continue; }
        let i = l.var as usize;
        if i < nvars {
            asgn[i] = l.neg;
        }
    }
    asgn
}

/// Matrix-method search via [`NNF::classify_paths_uncovered_only`] on
/// `comp` (the NNF of the formula's complement) under a SmartController.
/// Returns a satisfying assignment for the original CNF if an uncovered
/// path is found, UNSAT if the search exhausts, or Interrupted on
/// Ctrl-C.
///
/// When `show_progress` is true *and* stderr is a TTY, a live progress
/// bar is rendered on stderr — the cursor is hidden for the duration
/// and unconditionally restored on return (or panic) via
/// [`TerminalGuard`]'s `Drop` impl.
fn matrix_search(comp: NNF, nvars: usize, show_progress: bool) -> SearchOutcome {
    let total_paths = comp.path_count();
    let params = Some(PathParams {
        uncovered_path_limit: 1,           // stop after the first witness
        paths_class_limit:    usize::MAX,
        covered_prefix_limit: usize::MAX,
        no_cover:             true,        // pairs with `_uncovered_only`
    });
    let comp_for_path = comp.clone();
    let nnf_for_builder = comp.clone();
    let p = params.clone();

    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");

    rt.block_on(async move {
        let (handle, mut rx, cancel) = comp.classify_paths_uncovered_only(64,
            move |tx| smart_controller_builder(&nnf_for_builder, p, tx),
        );

        let want_progress = show_progress && io::stderr().is_terminal();
        let _term_guard = if want_progress { Some(TerminalGuard::new()) } else { None };

        let start = Instant::now();
        let progress_task = if want_progress {
            Some(tokio::spawn(matrix_progress_loop(cancel.clone(), total_paths, start)))
        } else {
            None
        };

        let mut path: Option<Vec<usize>> = None;
        let mut interrupted = false;
        loop {
            tokio::select! {
                msg = rx.recv() => match msg {
                    Some((PathsClass::Uncovered(p), _)) => { path = Some(p); break; }
                    Some(_) => continue,
                    None    => break,                       // worker drained → UNSAT
                },
                _ = tokio::signal::ctrl_c() => {
                    interrupted = true;
                    break;
                }
            }
        }

        cancel.cancel();
        drop(rx);
        if let Some(t) = progress_task { t.abort(); let _ = t.await; }
        let _ = handle.await;

        if interrupted {
            SearchOutcome::Interrupted
        } else if let Some(p) = path {
            let path_lits = comp_for_path.lits_on_path(&p);
            SearchOutcome::Sat(path_lits_to_assignment(nvars, &path_lits))
        } else {
            SearchOutcome::Unsat
        }
    })
}

/// CaDiCaL search.  Adds the DIMACS clauses to a `cadical::Solver`
/// directly (no Tseitin needed — they're already in CNF) and runs
/// `solve()` on a blocking thread, racing it against `tokio::signal::ctrl_c()`
/// for cancellation.
///
/// Progress is reported from the solver's `terminate` callback (which
/// CaDiCaL invokes ~periodically as a heartbeat): we throttle to 100ms
/// between renders and show learned-clause count, rate, and elapsed
/// time.  The Rust binding doesn't expose CaDiCaL's full statistics
/// counters, so this is the most useful proxy we can render without
/// extending the bindings.
fn cadical_search(nvars: usize, clauses: Vec<Vec<i32>>, show_progress: bool) -> SearchOutcome {
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    let cancel = Arc::new(AtomicBool::new(false));
    let cancel_for_solver = cancel.clone();

    let want_progress = show_progress && io::stderr().is_terminal();
    let start = Instant::now();

    let rt = tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .expect("tokio runtime");

    rt.block_on(async move {
        let _term_guard = if want_progress { Some(TerminalGuard::new()) } else { None };

        let solver_task = tokio::task::spawn_blocking(move || {
            let mut solver: cadical::Solver<CadicalProgressCallbacks> = cadical::Solver::new();
            solver.set_callbacks(Some(CadicalProgressCallbacks {
                cancel: cancel_for_solver,
                learned: 0,
                start,
                last_render: start,
                show_progress: want_progress,
            }));
            for clause in &clauses {
                solver.add_clause(clause.iter().copied());
            }
            let result = solver.solve();
            match result {
                Some(true) => {
                    // Extract truth values for each variable.  Free
                    // variables (`solver.value` returns None) default to
                    // `true` so the output stays a complete assignment.
                    let asgn: Vec<bool> = (1..=nvars).map(|v|
                        solver.value(v as i32).unwrap_or(true)
                    ).collect();
                    SolverResult::Sat(asgn)
                }
                Some(false) => SolverResult::Unsat,
                None        => SolverResult::Aborted,    // terminate() returned true
            }
        });

        // Race the solver against Ctrl-C.  On signal, set the cancel
        // flag; CaDiCaL's terminate callback will see it within ~ms and
        // bail.  Then await the task so the C++ solver tears down
        // cleanly before our runtime drops.
        let outcome = tokio::select! {
            res = solver_task => match res {
                Ok(SolverResult::Sat(asgn)) => SearchOutcome::Sat(asgn),
                Ok(SolverResult::Unsat)     => SearchOutcome::Unsat,
                Ok(SolverResult::Aborted)   => SearchOutcome::Interrupted,
                Err(_panic)                 => SearchOutcome::Interrupted,
            },
            _ = tokio::signal::ctrl_c() => {
                cancel.store(true, Ordering::Relaxed);
                // The select! consumed the solver_task future; we don't
                // need to await it again — but we'd like the solver to
                // finish its terminate poll before we exit so the C++
                // destructor runs cleanly.  In practice CaDiCaL's
                // terminate poll is ms-frequent so the runtime drop
                // happens essentially synchronously.
                SearchOutcome::Interrupted
            }
        };
        outcome
    })
}

/// Internal CaDiCaL solve outcome (intermediate: needs `_term_guard`
/// drop ordering and Ctrl-C race resolution before becoming a
/// [`SearchOutcome`]).
enum SolverResult {
    Sat(Vec<bool>),
    Unsat,
    Aborted,
}

/// CaDiCaL callbacks: tracks learned-clause count, polls the cancel
/// flag in `terminate`, and (when progress is enabled) re-renders the
/// progress line at most once every 100ms.
struct CadicalProgressCallbacks {
    cancel:        std::sync::Arc<std::sync::atomic::AtomicBool>,
    learned:       usize,
    start:         Instant,
    last_render:   Instant,
    show_progress: bool,
}

impl cadical::Callbacks for CadicalProgressCallbacks {
    fn max_length(&self) -> i32 { i32::MAX }

    fn learn(&mut self, _clause: &[i32]) {
        self.learned = self.learned.saturating_add(1);
    }

    fn terminate(&mut self) -> bool {
        if self.cancel.load(std::sync::atomic::Ordering::Relaxed) {
            return true;
        }
        if self.show_progress {
            let now = Instant::now();
            if now.duration_since(self.last_render) >= Duration::from_millis(100) {
                self.last_render = now;
                let elapsed = self.start.elapsed().as_secs_f64();
                render_cadical_progress(self.learned, elapsed);
            }
        }
        false
    }
}

fn render_cadical_progress(learned: usize, elapsed_secs: f64) {
    let rate = if elapsed_secs > 0.0 { learned as f64 / elapsed_secs } else { 0.0 };
    eprint!(
        "\r\x1b[2Kc CaDiCaL: {} learned ({}/s) {:.1}s",
        format_count(learned as f64),
        format_count(rate),
        elapsed_secs,
    );
    let _ = io::stderr().flush();
}

/// Tokio task that re-renders the matrix-search progress line every
/// 100ms until the search completes or the task is aborted.  Reads
/// `paths_so_far` off the `PathClassificationHandle` (published every
/// 4096 traversal steps by the wrapping
/// [`logic::controller::CancelController`]).
async fn matrix_progress_loop(
    cancel: PathClassificationHandle,
    total_paths: f64,
    start: Instant,
) {
    let mut interval = tokio::time::interval(Duration::from_millis(100));
    interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
    // Skip the first immediate tick so we don't render before any work
    // has happened (the first non-zero update arrives ~ms in).
    interval.tick().await;
    loop {
        interval.tick().await;
        let so_far = cancel.paths_so_far();
        let elapsed = start.elapsed().as_secs_f64();
        render_progress(so_far, total_paths, elapsed);
    }
}

/// Render one progress line on stderr.  Format roughly mirrors the web
/// app's path display: `bar | percent | so-far/total | rate | elapsed`.
fn render_progress(so_far: f64, total: f64, elapsed_secs: f64) {
    let pct = if total > 0.0 { (so_far / total * 100.0).clamp(0.0, 100.0) } else { 0.0 };
    let rate = if elapsed_secs > 0.0 { so_far / elapsed_secs } else { 0.0 };
    let bar_width = 30usize;
    let filled = ((pct / 100.0) * bar_width as f64).round() as usize;
    let filled = filled.min(bar_width);
    let bar: String = (0..bar_width)
        .map(|i| if i < filled { '█' } else { '·' })
        .collect();
    // \r returns to col 0; \x1b[2K clears the entire line.  Together
    // they overwrite the previous render in place without scrolling.
    eprint!(
        "\r\x1b[2Kc [{}] {:>5.1}% {}/{} ({}/s) {:.1}s",
        bar, pct,
        format_count(so_far),
        format_count(total),
        format_count(rate),
        elapsed_secs,
    );
    let _ = io::stderr().flush();
}

/// SI-prefix big-number formatter.  Keeps lines short on huge formulas
/// (`fault_add_at_most`-style problems can have 1.85e15 paths in the
/// complement).
fn format_count(n: f64) -> String {
    let abs = n.abs();
    if !n.is_finite() { "?".into() }
    else if abs < 1e3   { format!("{:.0}", n) }
    else if abs < 1e6   { format!("{:.1}K", n / 1e3) }
    else if abs < 1e9   { format!("{:.1}M", n / 1e6) }
    else if abs < 1e12  { format!("{:.1}G", n / 1e9) }
    else if abs < 1e15  { format!("{:.1}T", n / 1e12) }
    else if abs < 1e18  { format!("{:.1}P", n / 1e15) }
    else                { format!("{:.2e}", n) }
}

/// RAII cursor / progress-line manager.  On construction it hides the
/// cursor so the bar redraws don't blink; on drop it clears the bar
/// line and shows the cursor again.  Drop runs on normal completion,
/// panic unwinding, and tokio runtime shutdown — including after we
/// catch a Ctrl-C — so the user's terminal is left in a sane state.
struct TerminalGuard;

impl TerminalGuard {
    fn new() -> Self {
        // ESC[?25l = hide cursor.
        eprint!("\x1b[?25l");
        let _ = io::stderr().flush();
        TerminalGuard
    }
}

impl Drop for TerminalGuard {
    fn drop(&mut self) {
        // \r + ESC[2K = move to col 0 and clear line.  ESC[?25h = show cursor.
        eprint!("\r\x1b[2K\x1b[?25h");
        let _ = io::stderr().flush();
    }
}

/// Print the SAT-competition `v` line for the given assignment.
/// `asgn[i]` is the truth value of variable `i + 1` (1-based DIMACS):
/// `true` writes `+i`, `false` writes `-i`.  Output ends with the
/// `0` terminator the format requires.
fn write_v_line<W: io::Write>(w: &mut W, asgn: &[bool]) -> io::Result<()> {
    write!(w, "v")?;
    for (i, &val) in asgn.iter().enumerate() {
        let v = (i + 1) as i32;
        write!(w, " {}", if val { v } else { -v })?;
    }
    writeln!(w, " 0")
}

/// Parsed command-line flags.
struct Args {
    show_progress: bool,
    use_cadical:   bool,
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args { show_progress: false, use_cadical: false };
    for arg in std::env::args().skip(1) {
        match arg.as_str() {
            "--progress" | "-p" => a.show_progress = true,
            "--cadical"  | "-c" => a.use_cadical   = true,
            "--help"     | "-h" => {
                eprintln!("Usage: sat [--cadical] [--progress] < problem.cnf");
                eprintln!();
                eprintln!("  --cadical, -c     Solve via the bundled CaDiCaL solver instead");
                eprintln!("                    of the matrix-method search with SmartController.");
                eprintln!("  --progress, -p    Show a live progress bar on stderr (TTY only).");
                eprintln!("                    Press Ctrl-C to interrupt.");
                std::process::exit(0);
            }
            other => return Err(format!("unknown argument: {:?}", other)),
        }
    }
    Ok(a)
}

fn main() {
    let args = match parse_args() {
        Ok(a) => a,
        Err(e) => {
            eprintln!("c {}", e);
            std::process::exit(2);
        }
    };

    // Parse stdin (buffered) into a clause set.
    let stdin = io::stdin();
    let (nvars, clauses) = match parse_dimacs(stdin.lock()) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("c parse error: {}", e);
            std::process::exit(1);
        }
    };
    eprintln!("c parsed {} variables, {} clauses", nvars, clauses.len());

    // Quick edge cases handled before invoking either backend.
    if clauses.iter().any(|c| c.is_empty()) {
        println!("s UNSATISFIABLE");
        return;
    }
    if clauses.is_empty() {
        println!("s SATISFIABLE");
        let stdout = io::stdout();
        let mut w = stdout.lock();
        write_v_line(&mut w, &vec![true; nvars]).unwrap();
        return;
    }

    let backend = if args.use_cadical { "CaDiCaL" } else { "matrix+SmartController" };
    eprintln!("c backend: {}", backend);
    let t = Instant::now();
    let outcome = if args.use_cadical {
        cadical_search(nvars, clauses, args.show_progress)
    } else {
        matrix_search(cnf_complement_nnf(&clauses), nvars, args.show_progress)
    };
    let elapsed_ms = t.elapsed().as_secs_f64() * 1000.0;

    match outcome {
        SearchOutcome::Unsat => {
            eprintln!("c UNSAT in {:.1}ms", elapsed_ms);
            println!("s UNSATISFIABLE");
        }
        SearchOutcome::Sat(asgn) => {
            eprintln!("c SAT in {:.1}ms", elapsed_ms);
            println!("s SATISFIABLE");
            let stdout = io::stdout();
            let mut w = stdout.lock();
            write_v_line(&mut w, &asgn).unwrap();
        }
        SearchOutcome::Interrupted => {
            eprintln!("c INTERRUPTED after {:.1}ms", elapsed_ms);
            // Standard SIGINT exit code: 130 = 128 + SIGINT(2).
            std::process::exit(130);
        }
    }
}

// ─── Tests ────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// Solve a CNF via the matrix-method backend; returns the assignment
    /// directly on SAT, `Err(())` on UNSAT.
    fn solve(nvars: usize, clauses: &[Vec<i32>]) -> Result<Vec<bool>, ()> {
        if clauses.iter().any(|c| c.is_empty()) { return Err(()); }
        if clauses.is_empty() { return Ok(vec![true; nvars]); }
        let comp = cnf_complement_nnf(clauses);
        match matrix_search(comp, nvars, /*show_progress=*/ false) {
            SearchOutcome::Sat(asgn) => Ok(asgn),
            SearchOutcome::Unsat => Err(()),
            SearchOutcome::Interrupted => panic!("test search reported interrupted"),
        }
    }

    /// Solve a CNF via the CaDiCaL backend.  Same shape as `solve`.
    fn solve_cadical(nvars: usize, clauses: &[Vec<i32>]) -> Result<Vec<bool>, ()> {
        if clauses.iter().any(|c| c.is_empty()) { return Err(()); }
        if clauses.is_empty() { return Ok(vec![true; nvars]); }
        match cadical_search(nvars, clauses.to_vec(), /*show_progress=*/ false) {
            SearchOutcome::Sat(asgn) => Ok(asgn),
            SearchOutcome::Unsat => Err(()),
            SearchOutcome::Interrupted => panic!("test cadical_search reported interrupted"),
        }
    }

    /// Check that an assignment satisfies every clause of a CNF (every
    /// clause has at least one literal that evaluates to true).
    fn satisfies(clauses: &[Vec<i32>], asgn: &[bool]) -> bool {
        clauses.iter().all(|cl| cl.iter().any(|&lit| {
            let i = (lit.unsigned_abs() - 1) as usize;
            (lit > 0) == asgn[i]
        }))
    }

    /// Convenience: assert SAT and that the returned assignment really
    /// satisfies every clause.
    fn assert_sat(nvars: usize, clauses: &[Vec<i32>]) {
        let asgn = solve(nvars, clauses).expect("expected SAT, got UNSAT");
        assert!(satisfies(clauses, &asgn),
            "solver returned non-satisfying assignment {:?} for {:?}", asgn, clauses);
    }

    /// Convenience: assert UNSAT.
    fn assert_unsat(nvars: usize, clauses: &[Vec<i32>]) {
        assert!(solve(nvars, clauses).is_err(),
            "expected UNSAT, got SAT for {:?}", clauses);
    }

    // ── DIMACS parser ────────────────────────────────────────────────────

    #[test]
    fn parse_simple() {
        let input = b"c hello\np cnf 3 2\n1 -2 0\n2 3 0\n" as &[_];
        let (nvars, clauses) = parse_dimacs(input).unwrap();
        assert_eq!(nvars, 3);
        assert_eq!(clauses, vec![vec![1, -2], vec![2, 3]]);
    }

    #[test]
    fn parse_clause_spans_lines() {
        // Whitespace inside a clause is ignored; clauses can wrap.
        let input = b"p cnf 3 1\n1\n-2\n3 0\n" as &[_];
        let (nvars, clauses) = parse_dimacs(input).unwrap();
        assert_eq!(nvars, 3);
        assert_eq!(clauses, vec![vec![1, -2, 3]]);
    }

    #[test]
    fn parse_no_problem_line_infers_nvars() {
        // No `p cnf ...` header; nvars is inferred from max abs literal.
        let input = b"3 -7 0\n2 -1 0\n" as &[_];
        let (nvars, clauses) = parse_dimacs(input).unwrap();
        assert_eq!(nvars, 7);
        assert_eq!(clauses, vec![vec![3, -7], vec![2, -1]]);
    }

    #[test]
    fn parse_trailing_clause_without_zero() {
        // A trailing fragment with no `0` is still kept as a final clause.
        let input = b"p cnf 2 2\n1 -2 0\n1 2" as &[_];
        let (_, clauses) = parse_dimacs(input).unwrap();
        assert_eq!(clauses, vec![vec![1, -2], vec![1, 2]]);
    }

    #[test]
    fn parse_rejects_garbage() {
        let input = b"p cnf 1 1\n1 banana 0\n" as &[_];
        assert!(parse_dimacs(input).is_err());
    }

    // ── End-to-end SAT/UNSAT ─────────────────────────────────────────────

    #[test]
    fn sat_three_clauses() {
        // (x1 ∨ ¬x2) ∧ (x2 ∨ x3) ∧ (¬x1 ∨ ¬x3)
        assert_sat(3, &[vec![1, -2], vec![2, 3], vec![-1, -3]]);
    }

    #[test]
    fn unsat_two_var_exhaustive() {
        // All four 2-clause-of-2-lits combinations: contradicts every assignment.
        assert_unsat(2, &[vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]]);
    }

    #[test]
    fn sat_single_literal() {
        // x1
        assert_sat(1, &[vec![1]]);
    }

    #[test]
    fn unsat_single_literal_contradiction() {
        // x1 ∧ ¬x1
        assert_unsat(1, &[vec![1], vec![-1]]);
    }

    #[test]
    fn sat_empty_cnf() {
        // No clauses at all — trivially satisfiable.
        assert_sat(0, &[]);
        assert_sat(3, &[]);
    }

    #[test]
    fn unsat_empty_clause() {
        // An empty clause is the empty disjunction, ≡ false.
        assert_unsat(1, &[vec![]]);
        assert_unsat(3, &[vec![1, 2], vec![]]);   // even mixed with other clauses
    }

    // ── Pigeonhole (UNSAT for n+1 pigeons in n holes) ────────────────────

    /// Build the standard PHP encoding for `n_pigeons` pigeons and
    /// `n_holes` holes:
    /// - For each pigeon, at least one hole.
    /// - For each hole, no two pigeons share it.
    fn php(n_pigeons: usize, n_holes: usize) -> (usize, Vec<Vec<i32>>) {
        let var = |i: usize, j: usize| (n_holes * (i - 1) + j) as i32;
        let mut clauses = Vec::new();
        for i in 1..=n_pigeons {
            clauses.push((1..=n_holes).map(|j| var(i, j)).collect::<Vec<_>>());
        }
        for j in 1..=n_holes {
            for i in 1..=n_pigeons {
                for k in (i + 1)..=n_pigeons {
                    clauses.push(vec![-var(i, j), -var(k, j)]);
                }
            }
        }
        (n_pigeons * n_holes, clauses)
    }

    #[test]
    fn unsat_php_3_2() {
        let (n, c) = php(3, 2);
        assert_unsat(n, &c);
    }

    #[test]
    fn unsat_php_4_3() {
        let (n, c) = php(4, 3);
        assert_unsat(n, &c);
    }

    #[test]
    fn unsat_php_5_4() {
        let (n, c) = php(5, 4);
        assert_unsat(n, &c);
    }

    #[test]
    fn sat_php_n_n() {
        // 3 pigeons in 3 holes is SAT (the diagonal works).
        let (n, c) = php(3, 3);
        assert_sat(n, &c);
    }

    // ── Random 3-SAT at the easy ratio ───────────────────────────────────

    /// Tiny LCG so tests don't depend on a `rand` crate.
    fn lcg_next(state: &mut u64) -> u64 {
        *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *state
    }

    /// Build a random 3-CNF with a fixed seed.
    fn random_3sat(n_vars: usize, n_clauses: usize, seed: u64) -> Vec<Vec<i32>> {
        let mut state = seed;
        (0..n_clauses).map(|_| {
            // Pick three distinct vars uniformly.
            let mut chosen: Vec<i32> = Vec::with_capacity(3);
            while chosen.len() < 3 {
                let v = (lcg_next(&mut state) % (n_vars as u64)) as i32 + 1;
                if !chosen.iter().any(|&c| c.abs() == v) {
                    let sign = if lcg_next(&mut state) & 1 == 0 { 1 } else { -1 };
                    chosen.push(v * sign);
                }
            }
            chosen
        }).collect()
    }

    #[test]
    fn sat_random_3sat_easy() {
        // ratio 3.0 — well below the SAT/UNSAT phase transition (~4.27),
        // so SAT with high probability.
        let n = 30;
        let m = 90;
        let clauses = random_3sat(n, m, 42);
        assert_sat(n, &clauses);
    }

    // ── Progress / formatter helpers ─────────────────────────────────────

    #[test]
    fn format_count_si_prefixes() {
        assert_eq!(format_count(0.0),       "0");
        assert_eq!(format_count(42.0),      "42");
        assert_eq!(format_count(1_500.0),   "1.5K");
        assert_eq!(format_count(2_500_000.0), "2.5M");
        assert_eq!(format_count(7.0e9),     "7.0G");
        assert_eq!(format_count(3.0e12),    "3.0T");
        assert_eq!(format_count(1.85e15),   "1.9P");
        // Beyond Peta (rare but possible) falls back to scientific.
        assert!(format_count(1.0e20).contains('e'));
    }

    #[test]
    fn render_progress_doesnt_panic() {
        // Smoke test: render with various inputs (incl. degenerate
        // total=0 and start≈now) shouldn't panic or divide-by-zero.
        // Output goes to stderr, which captures during tests.
        render_progress(0.0,   0.0, 0.0);
        render_progress(50.0,  100.0, 1.5);
        render_progress(1e15,  1.85e15, 12.3);
        // Past-100% shouldn't overflow the bar.
        render_progress(150.0, 100.0, 1.0);
    }

    #[test]
    fn matrix_search_smoke() {
        // End-to-end check that `matrix_search` produces an Sat outcome
        // for a satisfiable formula and an Unsat outcome for a contradiction.
        match matrix_search(cnf_complement_nnf(&[vec![1, -2], vec![2, 3], vec![-1, -3]]), 3, false) {
            SearchOutcome::Sat(_) => {}
            other => panic!("expected Sat, got {:?}", outcome_kind(&other)),
        }
        match matrix_search(cnf_complement_nnf(&[vec![1], vec![-1]]), 1, false) {
            SearchOutcome::Unsat => {}
            other => panic!("expected Unsat, got {:?}", outcome_kind(&other)),
        }
    }

    #[test]
    fn cadical_search_smoke() {
        // Same shape as `matrix_search_smoke` but going through the
        // CaDiCaL backend.
        match cadical_search(3, vec![vec![1, -2], vec![2, 3], vec![-1, -3]], false) {
            SearchOutcome::Sat(_) => {}
            other => panic!("expected Sat, got {:?}", outcome_kind(&other)),
        }
        match cadical_search(1, vec![vec![1], vec![-1]], false) {
            SearchOutcome::Unsat => {}
            other => panic!("expected Unsat, got {:?}", outcome_kind(&other)),
        }
    }

    fn outcome_kind(o: &SearchOutcome) -> &'static str {
        match o {
            SearchOutcome::Sat(_)       => "Sat",
            SearchOutcome::Unsat        => "Unsat",
            SearchOutcome::Interrupted  => "Interrupted",
        }
    }

    /// Confirm both backends produce satisfying assignments for the
    /// random-3-SAT instance and the PHP-3-3 instance.
    #[test]
    fn cadical_agrees_on_phps_and_random() {
        let cases: Vec<(usize, Vec<Vec<i32>>, bool)> = vec![
            // (nvars, clauses, sat?)
            (3, vec![vec![1, -2], vec![2, 3], vec![-1, -3]], true),
            (1, vec![vec![1], vec![-1]], false),
            (php(3, 3).0, php(3, 3).1, true),
            (php(4, 3).0, php(4, 3).1, false),
            (30, random_3sat(30, 90, 42), true),
        ];
        for (n, c, want_sat) in cases {
            let r1 = solve(n, &c).is_ok();
            let r2 = solve_cadical(n, &c).is_ok();
            assert_eq!(r1, want_sat, "matrix backend disagreed on {:?}", &c);
            assert_eq!(r2, want_sat, "cadical backend disagreed on {:?}", &c);
            // For SAT, both assignments should actually satisfy.
            if want_sat {
                let a1 = solve(n, &c).unwrap();
                let a2 = solve_cadical(n, &c).unwrap();
                assert!(satisfies(&c, &a1), "matrix returned non-satisfying asgn");
                assert!(satisfies(&c, &a2), "cadical returned non-satisfying asgn");
            }
        }
    }

    #[test]
    fn cadical_render_progress_doesnt_panic() {
        render_cadical_progress(0, 0.0);
        render_cadical_progress(123_456, 4.5);
    }
}
