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
// `IsTerminal` is needed for the `.is_terminal()` method calls below
// but rustc occasionally flags it as unused in this edition; the
// allow keeps the warning out of the build.
#[allow(unused_imports)]
use std::io::{self, BufRead, IsTerminal, Write};
use std::time::{Duration, Instant};

use logic::matrix::{
    Lit, NNF, PathClassificationHandle, PathParams, PathsClass, Var,
    CdclController, DynOnClass, cdcl_controller_builder, smart_controller_builder,
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
/// Which matrix-method controller to drive the search with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MatrixBackend {
    /// `matrix.smart`: [`SmartController`](logic::controller::SmartController)
    /// — watched-literal propagation across Prod-of-`Lit`s clauses.
    Smart,
    /// `matrix.cdcl`: [`CdclController`](logic::controller::CdclController)
    /// — CDCL-flavoured controller with watched-literal BCP, 1UIP
    /// learning, and Luby restarts.
    Cdcl,
    /// `matrix.eff`: CDCL inner wrapped in
    /// [`EffectiveCountWrapper`](logic::dual::path_effective::EffectiveCountWrapper)
    /// for effective-path-count-aware Sum/Prod ordering and
    /// zero-count pruning.  Single-DFS — no dual A/B threads.
    Eff,
    /// `greedy×cdcl`: dual-framework search pairing
    /// [`GreedyMaxCoverController`](logic::dual::GreedyMaxCoverController)
    /// as the A-side cover ranker with
    /// [`CdclDualPathController`](logic::dual::CdclDualPathController)
    /// as the B-side path searcher.
    GreedyCdcl,
    /// `greedy×eff`: dual-framework search pairing greedy A with
    /// [`EffectivePathController`](logic::dual::EffectivePathController)
    /// (CDCL inner + Effective layer).  Currently the strongest
    /// matrix-method configuration on most structured benchmarks
    /// (faulty-adder, BMC).
    GreedyEff,
}

impl MatrixBackend {
    pub fn name(self) -> &'static str {
        match self {
            MatrixBackend::Smart      => "matrix.smart",
            MatrixBackend::Cdcl       => "matrix.cdcl",
            MatrixBackend::Eff        => "matrix.eff",
            MatrixBackend::GreedyCdcl => "greedy×cdcl",
            MatrixBackend::GreedyEff  => "greedy×eff",
        }
    }
}

fn matrix_search(comp: NNF, nvars: usize, show_progress: bool, backend: MatrixBackend) -> SearchOutcome {
    let total_paths = comp.path_count();
    let params = Some(PathParams {
        uncovered_path_limit: 1,           // stop after the first witness
        paths_class_limit:    usize::MAX,
        covered_prefix_limit: usize::MAX,
        no_cover:             true,        // pairs with `_uncovered_only`
    });
    let comp_for_path = comp.clone();

    // The matrix-method DFS in `for_each_path_prefix_ord` recurses
    // through Sum siblings via continuation closures.  On a CNF
    // complement with N clauses, the top-level Sum has N children, so
    // the traversal nests O(N) deep — for industrial inputs (100k+
    // clauses) that easily blows the default 2 MB tokio stack.
    //
    // Bumping `thread_stack_size` to 256 MB on the runtime builder
    // covers everything we've seen in the wild (≈ 1.3 KB per nested
    // frame × 200K frames ≈ 260 MB worst case).  The proper fix is to
    // rewrite the traversal as an explicit work-stack iteration; this
    // is the bandage until that lands.
    //
    // Multi-thread runtime (not current_thread): the dual backends'
    // `try_send` pattern keeps `rx.recv()` perpetually ready, which
    // on a single-thread runtime starves the IO driver and SIGINT
    // never gets delivered to the `ctrl_c` future.  With a
    // multi-thread runtime the IO driver runs on its own thread
    // and signal delivery is independent of how busy the consumer
    // loop is.  Two worker threads is plenty (one for the consumer
    // loop, one for the IO driver / blocking-pool coordinator);
    // the actual heavy lifting happens in spawn_blocking tasks
    // which use a separate blocking-thread pool anyway.
    let rt = tokio::runtime::Builder::new_multi_thread()
        .worker_threads(2)
        .enable_all()
        .thread_stack_size(256 * 1024 * 1024)
        .build()
        .expect("tokio runtime");

    rt.block_on(async move {
        // Pre-clone the inputs each builder branch needs so the
        // borrow checker is happy with the if/else producing the same
        // `(JoinHandle, Receiver, Handle)` tuple from two different
        // controller types.  Each branch is FnOnce so only one set of
        // clones is actually consumed.
        let nnf_smart = comp.clone();
        let nnf_cdcl  = comp.clone();
        let p_smart   = params.clone();
        let p_cdcl    = params.clone();
        let p_eff     = params.clone();
        let (handle, mut rx, cancel) = match backend {
            MatrixBackend::Smart => comp.classify_paths_uncovered_only(64,
                move |tx| smart_controller_builder(&nnf_smart, p_smart, tx),
            ),
            MatrixBackend::Cdcl => comp.classify_paths_uncovered_only(64,
                move |tx| cdcl_controller_builder(&nnf_cdcl, p_cdcl, tx),
            ),
            MatrixBackend::Eff => {
                // matrix.eff uses the positions-ON engine
                // (`classify_paths_with_nnf`) because
                // `EffectiveCountWrapper::sum_ord` re-orders Sum
                // children — the positions-OFF engine + downstream
                // `positions_on_path` is unsound for that.  The
                // `_with_nnf` builder passes the DFS-internal NNF
                // clone to the builder so the `EffectiveCountIndex`'s
                // pointer-keyed lookups line up with the &NNF refs the
                // engine passes via sum_ord / prod_ord.
                use logic::dual::effective_count::{EffectiveCountIndex, EffectiveCounts};
                use logic::dual::path_effective::EffectiveCountWrapper;
                comp.classify_paths_with_nnf(64, move |nnf_ref, tx| {
                    let on_class: DynOnClass = Box::new(move |class, hit_limit|
                        tx.blocking_send((class, hit_limit)).is_ok());
                    let cdcl = CdclController::for_nnf(nnf_ref, p_eff, on_class);
                    let idx = EffectiveCountIndex::build(nnf_ref);
                    let counts = EffectiveCounts::new(&idx);
                    EffectiveCountWrapper::new(cdcl, idx, counts)
                })
            }
            MatrixBackend::GreedyCdcl | MatrixBackend::GreedyEff => {
                spawn_dual_matrix_search(backend, comp.clone(), 64)
            }
        };

        let want_progress = show_progress && io::stderr().is_terminal();
        let _term_guard = if want_progress { Some(TerminalGuard::new()) } else { None };

        let start = Instant::now();
        let progress_task = if want_progress {
            Some(tokio::spawn(matrix_progress_loop(cancel.clone(), total_paths, start)))
        } else {
            None
        };

        let mut path: Option<Vec<usize>> = None;
        // SIGINT-listener task: spawned as an independent task so it
        // subscribes to `tokio::signal::ctrl_c()` exactly once and
        // stays subscribed for the whole run.  This avoids the
        // "fresh subscriber every loop iteration" pitfall of calling
        // `ctrl_c()` inside `select!` directly — a SIGINT that
        // arrived between two iterations would otherwise be lost
        // because no subscriber was alive at the moment it fired.
        // Spawning on the multi-thread runtime (configured above)
        // also keeps signal delivery independent of how busy the
        // main consume loop is.
        //
        // The main `select!` below races `rx.recv()` against the
        // signal task's `JoinHandle`.  `biased;` polls the signal
        // handle first so even when `rx.recv()` is also ready we
        // notice the interrupt promptly.
        let signal_task: tokio::task::JoinHandle<()> = tokio::spawn(async move {
            let _ = tokio::signal::ctrl_c().await;
        });
        let mut signal_task = signal_task;
        // Progress publishing is now done inside the search engine:
        // single-DFS backends via the `CancelController` wrapper, dual
        // backends via the `ProgressWrapper` (added to both
        // `EffectivePathController` and `CdclDualPathController`) which
        // publishes `paths_classified()` directly into the cancel
        // handle's paths atom.  So the consumer loop just drains
        // events for verdict purposes.
        loop {
            tokio::select! {
                biased;
                _ = &mut signal_task => {
                    // SIGINT received.  Restore the terminal (cursor
                    // visible, progress line cleared) BEFORE exiting
                    // — `std::process::exit` skips Drop impls, so
                    // `TerminalGuard::drop` wouldn't otherwise run.
                    // Then print the canonical "INTERRUPTED" line
                    // and exit the process immediately rather than
                    // trying to drive the dual A/B threads to a
                    // graceful stop — the dual's cooperative-cancel
                    // signal (`Some(0)` from
                    // `should_continue_on_prefix`) means "skip this
                    // branch" not "exit the whole DFS", so on large
                    // formulas the cancel-and-join sequence can
                    // take many seconds to fully drain.  The OS
                    // reaps all worker threads cleanly on
                    // process-exit.
                    restore_terminal();
                    let ms = start.elapsed().as_secs_f64() * 1000.0;
                    eprintln!("c INTERRUPTED after {:.1}ms", ms);
                    std::process::exit(130);   // 128 + SIGINT
                }
                msg = rx.recv() => match msg {
                    Some((PathsClass::Uncovered(up), _)) => { path = Some(up.prod_path); break; }
                    Some(_) => continue,
                    None    => break,                       // worker drained → UNSAT
                },
            }
        }
        // Normal-completion path (Sat found or worker drained).  The
        // signal task is still running and will keep listening for
        // SIGINT indefinitely; abort it so the runtime can drop
        // cleanly.  Do NOT re-await — `select!` already
        // polled-to-completion any handle that wakes it, and tokio
        // panics on a second poll of a completed `JoinHandle`.
        // abort() on a not-yet-completed handle is the right call;
        // on an already-completed handle it's a harmless no-op.
        signal_task.abort();

        // Normal-completion shutdown.  (SIGINT path exited the
        // process via `std::process::exit(130)` above.)
        cancel.cancel();
        drop(rx);
        if let Some(t) = progress_task { t.abort(); let _ = t.await; }
        let _ = handle.await;

        if let Some(p) = path {
            let path_lits = comp_for_path.lits_on_path(&p);
            SearchOutcome::Sat(path_lits_to_assignment(nvars, &path_lits))
        } else {
            SearchOutcome::Unsat
        }
    })
}

/// Set up a dual-framework (`solve_dual_with_cancel`) search and
/// adapt it to the same `(JoinHandle, Receiver, PathClassificationHandle)`
/// shape `matrix_search` consumes for the single-DFS backends.  The
/// dual's B-side path controller is built with `with_stream(tx)` so
/// every `PathsClass` event B emits is tee'd onto the channel just
/// like a single-DFS controller would.  The UI cancel atomic is
/// shared with `solve_dual_with_cancel`'s `external_cancel` via
/// `PathClassificationHandle::cancel_flag()` — Ctrl-C propagates to
/// the dual within ~5 ms (`solve_dual_with_cancel`'s poll cadence).
fn spawn_dual_matrix_search(
    backend: MatrixBackend,
    target_nnf: NNF,
    buffer_size: usize,
) -> (
    tokio::task::JoinHandle<Result<(), Box<dyn std::error::Error + Send>>>,
    tokio::sync::mpsc::Receiver<(PathsClass, bool)>,
    PathClassificationHandle,
) {
    use logic::dual::{
        solve_dual_with_cancel, BasicCoverState, CdclDualPathController,
        EffectivePathController, GreedyMaxCoverController, SearchMode,
    };

    let (tx, rx) = tokio::sync::mpsc::channel::<(PathsClass, bool)>(buffer_size);
    let cancel = PathClassificationHandle::new();
    let external_cancel = cancel.cancel_flag();
    // Share the cancel handle's paths atom with the dual's path
    // controller so it can publish progress directly — the dual
    // doesn't get the `CancelController`-wrapping that single-DFS
    // controllers receive, so without this the progress bar would
    // stay at 0% for the whole run (especially noticeable for
    // greedy_eff, where the Effective layer prunes paths *before*
    // they reach the leaf-level Covered detection that would
    // populate `paths_classified` from event counting alone).
    let progress_atom = cancel.paths_atom();

    let handle = tokio::task::spawn_blocking(move || {
        let _ = match backend {
            MatrixBackend::GreedyCdcl => {
                let cover = GreedyMaxCoverController::default();
                let path  = CdclDualPathController::<BasicCoverState>::with_stream(tx)
                    .with_progress(progress_atom);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            MatrixBackend::GreedyEff => {
                let cover = GreedyMaxCoverController::default();
                let path  = EffectivePathController::<BasicCoverState>::with_stream(tx)
                    .with_progress(progress_atom);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            _ => unreachable!("spawn_dual_matrix_search called with non-dual backend"),
        };
        Ok::<(), Box<dyn std::error::Error + Send>>(())
    });
    (handle, rx, cancel)
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
/// Falls back to an indeterminate spinner when neither the count nor
/// the total are usable (very large formulas where `total = ∞`, or the
/// rare case of a backend that publishes no progress at all).
fn render_progress(so_far: f64, total: f64, elapsed_secs: f64) {
    let bar_width = 30usize;
    let have_total = total.is_finite() && total > 0.0;
    let have_progress = so_far > 0.0 && have_total;
    if !have_progress {
        // Indeterminate-progress mode: animate a small marker
        // sliding along the bar.  Triggered when `total` is `inf`
        // (path count overflowed f64 on huge formulas) or when
        // `so_far` is still 0.  Period ~3 s.  The renderer is
        // called every 100 ms by the progress loop, so position
        // advances by 1 each frame.
        let frame = (elapsed_secs * 10.0) as usize;
        let pos = frame % bar_width;
        let bar: String = (0..bar_width)
            .map(|i| if i == pos { '◉' } else { '·' })
            .collect();
        let rate = if elapsed_secs > 0.0 { so_far / elapsed_secs } else { 0.0 };
        eprint!(
            "\r\x1b[2Kc [{}] {}/{} ({}/s) {:.1}s",
            bar,
            format_count(so_far),
            format_count(total),
            format_count(rate),
            elapsed_secs,
        );
        let _ = io::stderr().flush();
        return;
    }
    let pct = (so_far / total * 100.0).clamp(0.0, 100.0);
    let rate = if elapsed_secs > 0.0 { so_far / elapsed_secs } else { 0.0 };
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
/// cursor (so progress-bar redraws don't blink) AND installs a
/// best-effort panic hook + a few signal handlers that all call
/// `restore_terminal()` so the user's terminal is left in a sane
/// state across the modes of program exit we care about:
///
/// - **Normal completion / await of `handle.await`** — `Drop` runs.
/// - **Panic unwinding** — `Drop` runs as the stack unwinds.
/// - **`std::process::exit(130)` from the SIGINT path** — explicit
///   `restore_terminal()` call before exit (see `matrix_search`).
/// - **Tokio runtime shutdown after Ctrl-C** — `Drop` runs when the
///   runtime drops the future.
/// - **Process abort (stack overflow, abort intrinsic, fatal
///   signal)** — handled by the libc signal handlers installed
///   below.  Signal-handler context restricts us to async-signal-safe
///   functions, so we write the restore bytes via the `write`
///   syscall directly rather than going through Rust's `print!`
///   machinery.
///
/// The panic hook chains the previous hook so the default Rust
/// panic message still prints.
struct TerminalGuard;

/// Write the cursor-restore + clear-line escape bytes via the raw
/// `write` syscall.  Async-signal-safe and panic-safe — fine to
/// call from signal handlers, panic hooks, and `Drop`.
fn restore_terminal() {
    // \r + ESC[2K = move to col 0 and clear line.  ESC[?25h = show cursor.
    const BYTES: &[u8] = b"\r\x1b[2K\x1b[?25h";
    // SAFETY: `write(2)` is async-signal-safe.  fd 2 is stderr.  The
    // buffer is a 'static slice so it's always valid.  We ignore the
    // return value because there's nothing useful to do if it fails
    // (we're typically on the way out anyway).
    unsafe {
        let _ = libc::write(
            libc::STDERR_FILENO,
            BYTES.as_ptr() as *const libc::c_void,
            BYTES.len(),
        );
    }
}

/// Signal handler for abrupt-termination signals (SIGABRT, SIGSEGV,
/// SIGBUS, SIGFPE).  Restores the terminal then re-raises the signal
/// with the default disposition so the process dies the way it was
/// going to die anyway (core dump, exit code reflecting the signal).
extern "C" fn restore_and_reraise(sig: libc::c_int) {
    restore_terminal();
    // Reset to default handler and re-raise.  This way the process
    // exits with the right status and any debugger/core-dump setup
    // works as expected.
    unsafe {
        libc::signal(sig, libc::SIG_DFL);
        libc::raise(sig);
    }
}

impl TerminalGuard {
    fn new() -> Self {
        // ESC[?25l = hide cursor.
        eprint!("\x1b[?25l");
        let _ = io::stderr().flush();

        // Panic hook: chain restore-terminal in front of the existing
        // hook (default Rust panic printer, or whatever was set
        // before this).  Set inside `new()` so we only pay the cost
        // when a progress display is actually active.
        let prev_hook = std::panic::take_hook();
        std::panic::set_hook(Box::new(move |info| {
            restore_terminal();
            prev_hook(info);
        }));

        // Signal handlers for hard-abort scenarios that wouldn't
        // otherwise reach a Rust panic handler — stack overflow
        // typically delivers SIGABRT or SIGSEGV depending on the
        // platform; SIGBUS / SIGFPE are listed for completeness.
        // SIGINT is NOT registered here: it's already handled by
        // tokio's signal driver + our `signal_task`, which gives
        // the process a chance to clean up gracefully before
        // `std::process::exit(130)`.
        for sig in &[libc::SIGABRT, libc::SIGSEGV, libc::SIGBUS, libc::SIGFPE] {
            unsafe {
                libc::signal(*sig, restore_and_reraise as *const () as libc::sighandler_t);
            }
        }

        TerminalGuard
    }
}

impl Drop for TerminalGuard {
    fn drop(&mut self) {
        restore_terminal();
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

/// What kind of search to run.  Either a `MatrixBackend` (the
/// matrix-method path-search variants) or CaDiCaL (the bundled
/// reference SAT solver).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BackendChoice {
    Matrix(MatrixBackend),
    Cadical,
}

impl BackendChoice {
    fn name(self) -> &'static str {
        match self {
            BackendChoice::Matrix(m) => m.name(),
            BackendChoice::Cadical   => "cadical",
        }
    }

    /// Parse a `--backend NAME` argument value.  Accepts the canonical
    /// names from the bench/UI (`smart`, `cdcl`, `eff`, `greedy_cdcl`,
    /// `greedy_eff`, `cadical`) plus a few aliases for convenience.
    fn parse(s: &str) -> Result<Self, String> {
        match s {
            "smart"      | "matrix.smart"  => Ok(BackendChoice::Matrix(MatrixBackend::Smart)),
            "cdcl"       | "matrix.cdcl"   => Ok(BackendChoice::Matrix(MatrixBackend::Cdcl)),
            "eff"        | "matrix.eff"    => Ok(BackendChoice::Matrix(MatrixBackend::Eff)),
            "greedy_cdcl" | "greedy×cdcl"
                         | "greedyxcdcl"   => Ok(BackendChoice::Matrix(MatrixBackend::GreedyCdcl)),
            "greedy_eff" | "greedy×eff"
                         | "greedyxeff"    => Ok(BackendChoice::Matrix(MatrixBackend::GreedyEff)),
            "cadical"                      => Ok(BackendChoice::Cadical),
            _ => Err(format!(
                "unknown backend {:?}; expected one of: smart, cdcl, eff, \
                 greedy_cdcl, greedy_eff, cadical", s
            )),
        }
    }
}

/// Parsed command-line flags.
struct Args {
    show_progress: bool,
    backend:       BackendChoice,
}

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        show_progress: false,
        backend: BackendChoice::Matrix(MatrixBackend::Smart),
    };
    let mut explicit_backend = false;
    let mut iter = std::env::args().skip(1);
    while let Some(arg) = iter.next() {
        match arg.as_str() {
            "--progress" | "-p" => a.show_progress = true,
            // Unified backend selector — preferred form.
            "--backend"  | "-b" => {
                let v = iter.next().ok_or_else(||
                    "--backend requires a value (e.g. --backend greedy_eff)".to_string())?;
                a.backend = BackendChoice::parse(&v)?;
                explicit_backend = true;
            }
            s if s.starts_with("--backend=") => {
                a.backend = BackendChoice::parse(&s["--backend=".len()..])?;
                explicit_backend = true;
            }
            // Legacy boolean aliases — keep so older invocations
            // still work.  Mutually exclusive with each other (and
            // with --backend, since --backend is "the new way").
            "--cadical"  | "-c" => {
                if explicit_backend {
                    return Err("--cadical conflicts with --backend".into());
                }
                a.backend = BackendChoice::Cadical;
                explicit_backend = true;
            }
            "--cdcl"            => {
                if explicit_backend {
                    return Err("--cdcl conflicts with --backend".into());
                }
                a.backend = BackendChoice::Matrix(MatrixBackend::Cdcl);
                explicit_backend = true;
            }
            "--help"     | "-h" => {
                eprintln!("Usage: sat [--backend NAME] [--progress] < problem.cnf");
                eprintln!();
                eprintln!("  --backend NAME, -b NAME");
                eprintln!("                    Select the search backend.  NAME is one of:");
                eprintln!("                      smart        — matrix.smart (default)");
                eprintln!("                                     SmartController, single-DFS");
                eprintln!("                      cdcl         — matrix.cdcl");
                eprintln!("                                     CdclController, single-DFS");
                eprintln!("                      eff          — matrix.eff");
                eprintln!("                                     CdclController + Effective layer,");
                eprintln!("                                     single-DFS, no dual overhead");
                eprintln!("                      greedy_cdcl  — greedy × CdclDualPath, dual");
                eprintln!("                      greedy_eff   — greedy × Effective + CDCL, dual");
                eprintln!("                                     (strongest on structured benches)");
                eprintln!("                      cadical      — bundled CaDiCaL reference solver");
                eprintln!("  --cadical, -c     Legacy alias for --backend cadical.");
                eprintln!("  --cdcl            Legacy alias for --backend cdcl.");
                eprintln!("  --progress, -p    Show a live progress bar on stderr (TTY only).");
                eprintln!("                    Press Ctrl-C to interrupt.");
                eprintln!();
                eprintln!("Default backend: smart (matrix.smart).");
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

    eprintln!("c backend: {}", args.backend.name());
    let t = Instant::now();
    let outcome = match args.backend {
        BackendChoice::Cadical => cadical_search(nvars, clauses, args.show_progress),
        BackendChoice::Matrix(m) =>
            matrix_search(cnf_complement_nnf(&clauses), nvars, args.show_progress, m),
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

    /// Solve a CNF via the matrix-method backend with the
    /// SmartController.  Returns the assignment directly on SAT,
    /// `Err(())` on UNSAT.
    fn solve(nvars: usize, clauses: &[Vec<i32>]) -> Result<Vec<bool>, ()> {
        solve_with_matrix(nvars, clauses, MatrixBackend::Smart)
    }

    /// Solve a CNF via the matrix-method backend with the
    /// (in-development) CdclController.
    fn solve_cdcl(nvars: usize, clauses: &[Vec<i32>]) -> Result<Vec<bool>, ()> {
        solve_with_matrix(nvars, clauses, MatrixBackend::Cdcl)
    }

    /// Shared body of `solve` / `solve_cdcl`.
    fn solve_with_matrix(nvars: usize, clauses: &[Vec<i32>], backend: MatrixBackend) -> Result<Vec<bool>, ()> {
        if clauses.iter().any(|c| c.is_empty()) { return Err(()); }
        if clauses.is_empty() { return Ok(vec![true; nvars]); }
        let comp = cnf_complement_nnf(clauses);
        match matrix_search(comp, nvars, /*show_progress=*/ false, backend) {
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
        // for a satisfiable formula and an Unsat outcome for a contradiction
        // across every matrix backend the binary exposes.
        for backend in [
            MatrixBackend::Smart,
            MatrixBackend::Cdcl,
            MatrixBackend::Eff,
            MatrixBackend::GreedyCdcl,
            MatrixBackend::GreedyEff,
        ] {
            match matrix_search(cnf_complement_nnf(&[vec![1, -2], vec![2, 3], vec![-1, -3]]), 3, false, backend) {
                SearchOutcome::Sat(_) => {}
                other => panic!("[{:?}] expected Sat, got {:?}", backend, outcome_kind(&other)),
            }
            match matrix_search(cnf_complement_nnf(&[vec![1], vec![-1]]), 1, false, backend) {
                SearchOutcome::Unsat => {}
                other => panic!("[{:?}] expected Unsat, got {:?}", backend, outcome_kind(&other)),
            }
        }
    }

    /// Cross-check: SmartController and CdclController must agree on
    /// every existing test case.  Both should produce a satisfying
    /// assignment (verified via `satisfies`) or both should report UNSAT.
    /// The actual assignments may differ — there's no guarantee the two
    /// search orderings hit the same witness.
    #[test]
    fn cdcl_agrees_with_smart_on_all_cases() {
        let cases: Vec<(usize, Vec<Vec<i32>>, bool)> = vec![
            (3, vec![vec![1, -2], vec![2, 3], vec![-1, -3]], true),
            (2, vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]], false),
            (1, vec![vec![1]], true),
            (1, vec![vec![1], vec![-1]], false),
            (php(3, 3).0, php(3, 3).1, true),
            (php(3, 2).0, php(3, 2).1, false),
            (php(4, 3).0, php(4, 3).1, false),
            (30, random_3sat(30, 90, 42), true),
        ];
        for (n, c, want_sat) in cases {
            let r_smart = solve(n, &c);
            let r_cdcl = solve_cdcl(n, &c);
            assert_eq!(r_smart.is_ok(), want_sat, "Smart disagreed on {:?}", &c);
            assert_eq!(r_cdcl.is_ok(), want_sat,  "Cdcl disagreed on {:?}",  &c);
            if want_sat {
                assert!(satisfies(&c, &r_smart.unwrap()), "Smart returned non-satisfying asgn");
                assert!(satisfies(&c, &r_cdcl.unwrap()),  "Cdcl returned non-satisfying asgn");
            }
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
