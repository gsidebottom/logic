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

use std::sync::{Arc, Mutex};
use std::sync::atomic::{AtomicBool, AtomicU8, Ordering};

use logic::matrix::{
    Lit, NNF, PathClassificationHandle, PathParams, PathsClass, Var,
    CdclController, DynOnClass, SmartController, cdcl_controller_builder, smart_controller_builder,
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

/// Classify a preprocessed NNF for an early-exit verdict.
///
/// NNF identity elements:
/// * `Prod(vec![])` = empty conjunction = `T` ⇒ formula is
///   trivially satisfiable; reconstruct any forced witness from the
///   recon stack and report SAT without running the search.
/// * `Sum(vec![])`  = empty disjunction = `F` ⇒ formula is
///   trivially unsatisfiable; report UNSAT.
/// * Everything else ⇒ search must run on `pp.nnf.complement()`.
enum PreprocessVerdict { TriviallySat, TriviallyUnsat, NeedsSearch }

fn preprocess_verdict(nnf: &NNF) -> PreprocessVerdict {
    match nnf {
        NNF::Prod(c) if c.is_empty() => PreprocessVerdict::TriviallySat,
        NNF::Sum(c)  if c.is_empty() => PreprocessVerdict::TriviallyUnsat,
        _ => PreprocessVerdict::NeedsSearch,
    }
}

/// Build the original CNF as an NNF — `Prod(Sum(lit, ...), ...)`,
/// no complement.  Used by the `--preprocess` path: NNF-level unit
/// propagation runs in the SAT direction (i.e. on `F`), then the
/// matrix-method search runs on the complement of the *simplified*
/// `F` — so we need both an `F` builder (this) and a `complement(F)`
/// builder ([`cnf_complement_nnf`]).
fn cnf_to_nnf(clauses: &[Vec<i32>]) -> NNF {
    if clauses.is_empty() {
        // Empty CNF is trivially true (the empty conjunction).
        return NNF::Prod(vec![]);
    }
    let clauses_nnf: Vec<NNF> = clauses.iter().map(|cl| {
        if cl.is_empty() {
            // Empty clause is false (the empty disjunction); the
            // outer code short-circuits UNSAT before getting here,
            // but include the case for completeness.
            NNF::Sum(vec![])
        } else {
            let lits: Vec<NNF> = cl.iter().map(|&n| {
                let var: Var = (n.unsigned_abs() - 1) as Var;
                // DIMACS sign: negative ⇒ negated literal.
                let neg = n < 0;
                NNF::Lit(Lit { var, neg })
            }).collect();
            if lits.len() == 1 { lits.into_iter().next().unwrap() } else { NNF::Sum(lits) }
        }
    }).collect();
    if clauses_nnf.len() == 1 {
        clauses_nnf.into_iter().next().unwrap()
    } else {
        NNF::Prod(clauses_nnf)
    }
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
    /// `matrix.eff_cover`: same Effective policy as [`Self::Eff`] but
    /// run on the cover-emitting **NNF** single-DFS engine (the one
    /// `cdcl`/`smart` use) instead of the arena engine, so it CAN emit
    /// a matrix UNSAT cover certificate via `--emit-cover`.  This is
    /// the substrate the open-evolution harness runs on: the shared
    /// `EffectiveCountWrapper` policy (the EVOLVE-BLOCK fns) drives the
    /// search, while `CdclController::for_nnf_with_cover` emits a
    /// complete static cover that `sat-cover-verify` checks — so an
    /// unsound (aggressively-pruning) policy that wrongly reports UNSAT
    /// is caught by an incomplete/failing certificate.  Slower than the
    /// arena `Eff` (NNF engine + position tracking), so it's a
    /// proof/evaluation substrate, not the production fast path.
    EffCover,
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
    /// `basic×eff`: dual-framework search pairing the minimal
    /// [`BasicCoverController`](logic::dual::BasicCoverController)
    /// A side (no upfront pair-mining — A only consumes pairs B
    /// emits) with [`EffectivePathController`].  Cheaper than
    /// `greedy×eff` on large CNFs where Greedy's
    /// `mine_pairs(nnf)` cost (O(N²) over clauses) dominates the
    /// actual search.
    BasicEff,
    /// `matrix.effb`: same controller stack as
    /// [`Self::Eff`] (CDCL + Effective wrapper on the arena
    /// engine), but with the engine's multi-level bubble-up
    /// re-enabled — `Some(k>0)` from a restart signal propagates
    /// `Some(k-1)` up through Prod/Sum frames instead of
    /// exhausting each sibling one at a time.
    ///
    /// **EXPERIMENTAL — known soundness issue.**  See
    /// [`logic::nnf_arena::NnfArena::for_each_path_prefix_bubble_up`]
    /// for the wrong-UNSAT mode the bubble-up can trigger.  Use
    /// only for benchmarking; verify every UNSAT against a trusted
    /// backend before trusting the result.
    Effb,
    /// `greedy×effb`: like [`Self::GreedyEff`] but with the NNF
    /// engine's bubble-up re-enabled.  Same soundness caveat as
    /// [`Self::Effb`].
    GreedyEffb,
    /// `basic×effb`: like [`Self::BasicEff`] but with the NNF
    /// engine's bubble-up re-enabled.  Same soundness caveat as
    /// [`Self::Effb`].
    BasicEffb,
}

impl MatrixBackend {
    pub fn name(self) -> &'static str {
        match self {
            MatrixBackend::Smart      => "matrix.smart",
            MatrixBackend::Cdcl       => "matrix.cdcl",
            MatrixBackend::Eff        => "matrix.eff",
            MatrixBackend::EffCover   => "matrix.eff_cover",
            MatrixBackend::GreedyCdcl => "greedy×cdcl",
            MatrixBackend::GreedyEff  => "greedy×eff",
            MatrixBackend::BasicEff   => "basic×eff",
            MatrixBackend::Effb       => "matrix.effb",
            MatrixBackend::GreedyEffb => "greedy×effb",
            MatrixBackend::BasicEffb  => "basic×effb",
        }
    }
}

/// Writer state for an open cover file.  Accumulates a *var-grouped*
/// cover (cert format v3): for each CNF variable, the set of
/// positions where the positive literal appears and the set where
/// the negative literal appears (in the matrix-method complement
/// NNF, the "lit visited at position (c, l)" is `-F[c][l]`, so
/// positive-lit positions are where the original CNF has the
/// negative literal, and vice versa).
///
/// **Cross-product semantics**: a pair `(p, q)` is implicitly in
/// the cert iff there exists some variable X with `p` in X's
/// positive-position set and `q` in X's negative-position set.
/// The verifier knows this and uses per-variable matched-counter
/// pruning instead of per-pair lookup.
///
/// **Compression**: on RoundRobin-scale inputs where each variable
/// appears at ~200 positions per polarity, the var-grouped form
/// stores 400 positions per variable instead of 40,000 pairs — a
/// ~100× space saving.
///
/// **Emission timing**: pairs accumulate in memory until
/// `finalize()` is called (or the struct drops).  This is by
/// design: the grouping requires seeing all pairs before we know
/// what to dedup.  Memory cost is bounded by the total number of
/// distinct (var, polarity, position) tuples in F, which is O(M)
/// where M is the number of clause-positions in the input —
/// always much smaller than the implied pair count.
struct CoverWriter {
    writer: io::BufWriter<std::fs::File>,
    /// Per-variable positive-polarity position sets.  Key: DIMACS
    /// variable index (1-based).  Value: set of `(clause_idx,
    /// lit_idx)` positions where the matrix-method lit at that
    /// position is `+var`.
    positive: std::collections::HashMap<u32, std::collections::HashSet<(usize, usize)>>,
    /// Mirror of `positive` but for negative-polarity positions
    /// (matrix-method lit `−var`).
    negative: std::collections::HashMap<u32, std::collections::HashSet<(usize, usize)>>,
    /// The original CNF clauses, used to resolve positions to lit
    /// values.  At position `(c, l)` the matrix-method engine sees
    /// `Lit::from_dimacs(-clauses[c][l])` — the negation of the
    /// original CNF lit, since the engine walks the complement NNF.
    clauses: std::sync::Arc<Vec<Vec<i32>>>,
}

impl CoverWriter {
    fn new(file: std::fs::File, clauses: std::sync::Arc<Vec<Vec<i32>>>) -> Self {
        Self {
            writer: io::BufWriter::new(file),
            positive: std::collections::HashMap::new(),
            negative: std::collections::HashMap::new(),
            clauses,
        }
    }

    /// Resolve a position `(c, l)` to the matrix-method lit at that
    /// spot — `-F[c][l]` as a `(var, neg)` pair.  Returns `None`
    /// for out-of-bounds or unexpected (non-length-2) positions.
    fn position_lit(&self, pos: &logic::matrix::Position) -> Option<(u32, bool)> {
        if pos.len() != 2 { return None; }
        let (c, l) = (pos[0], pos[1]);
        if c >= self.clauses.len() || l >= self.clauses[c].len() {
            return None;
        }
        // matrix-method walks the complement, so visited lit =
        // -F[c][l].  In DIMACS: positive int -> var, neg bit; we
        // flip the sign here for the complement-walk semantics.
        let orig = self.clauses[c][l];
        let visited = -orig;
        let var = visited.unsigned_abs();
        let neg = visited < 0;
        Some((var, neg))
    }

    /// Record `cpp`'s cover pair into the per-variable accumulators.
    /// Both positions must resolve to a valid `(var, neg)` and the
    /// two lits must be complementary (same var, opposite signs);
    /// otherwise the pair is silently dropped (= invariant violated
    /// on the prover side, not actionable here).
    fn maybe_write(&mut self, cpp: &logic::matrix::CoveredPathPrefix) -> io::Result<()> {
        let Some((va, na)) = self.position_lit(&cpp.cover.0) else { return Ok(()); };
        let Some((vb, nb)) = self.position_lit(&cpp.cover.1) else { return Ok(()); };
        if va != vb || na == nb { return Ok(()); }   // not a complementary pair
        // a is positive-lit, b is negative-lit (or vice versa).
        // Order so we insert into the right set.
        let (pos_pos, neg_pos) = if !na { (&cpp.cover.0, &cpp.cover.1) }
                                 else  { (&cpp.cover.1, &cpp.cover.0) };
        self.positive.entry(va)
            .or_insert_with(std::collections::HashSet::new)
            .insert((pos_pos[0], pos_pos[1]));
        self.negative.entry(va)
            .or_insert_with(std::collections::HashSet::new)
            .insert((neg_pos[0], neg_pos[1]));
        Ok(())
    }

    /// Number of distinct positions accumulated (across all
    /// variables, both polarities).  Useful as a cert-size proxy
    /// for the post-search footer.  Currently unused but kept as a
    /// stable diagnostic for future tooling that wants to report
    /// position-budget vs implied-pair counts side by side.
    #[allow(dead_code)]
    fn distinct_positions(&self) -> usize {
        self.positive.values().map(|s| s.len()).sum::<usize>()
            + self.negative.values().map(|s| s.len()).sum::<usize>()
    }

    /// Write the accumulated cover out in v3 format.  Idempotent
    /// (safe to call multiple times).
    fn finalize<S: AsRef<str>>(&mut self, verdict: S) -> io::Result<()> {
        // Iterate vars in sorted order so the output is
        // deterministic.  Collect once to release borrows.
        let mut vars: Vec<u32> = self.positive.keys()
            .chain(self.negative.keys())
            .copied()
            .collect();
        vars.sort();
        vars.dedup();
        let n_vars = vars.len();
        let n_pairs = self.implied_pair_count();
        for v in vars {
            let pos_set = self.positive.get(&v).cloned().unwrap_or_default();
            let neg_set = self.negative.get(&v).cloned().unwrap_or_default();
            // Skip vars that have only one polarity — no implied
            // pairs, so no contribution to the cover.
            if pos_set.is_empty() || neg_set.is_empty() { continue; }
            write!(self.writer, "v {} +", v)?;
            Self::write_clause_grouped(&mut self.writer, &pos_set)?;
            write!(self.writer, " -")?;
            Self::write_clause_grouped(&mut self.writer, &neg_set)?;
            writeln!(self.writer)?;
        }
        writeln!(self.writer, "# verdict {} ({} vars, {} implied pairs)",
                 verdict.as_ref(), n_vars, n_pairs)?;
        self.writer.flush()
    }

    /// Format a set of positions as space-separated `c:l[,l...]`
    /// tokens, grouping multiple lit indices of the same clause
    /// into one token with comma-separated lit-idx tail.
    fn write_clause_grouped<W: io::Write>(
        w: &mut W,
        positions: &std::collections::HashSet<(usize, usize)>,
    ) -> io::Result<()> {
        // Sort: by clause asc, then lit asc.  Stable + deterministic.
        let mut sorted: Vec<(usize, usize)> = positions.iter().copied().collect();
        sorted.sort();
        let mut i = 0;
        while i < sorted.len() {
            let (c, l) = sorted[i];
            write!(w, " {}:{}", c, l)?;
            // Group subsequent entries with the same clause as
            // comma-separated lit-idx suffixes.
            let mut j = i + 1;
            while j < sorted.len() && sorted[j].0 == c {
                write!(w, ",{}", sorted[j].1)?;
                j += 1;
            }
            i = j;
        }
        Ok(())
    }

    /// Sum over vars of |positive positions| * |negative positions|
    /// — the number of pairs the var-grouped cert implicitly
    /// represents.  Reported in the verdict footer for diagnostics.
    fn implied_pair_count(&self) -> usize {
        let mut total = 0usize;
        for (v, pos_set) in &self.positive {
            if let Some(neg_set) = self.negative.get(v) {
                total = total.saturating_add(pos_set.len() * neg_set.len());
            }
        }
        total
    }
}

/// `DratWriter` — emit a DRAT (Delete Resolution Asymmetric Tautology)
/// proof file alongside the search.  DRAT is the SAT-competition
/// standard proof format: a sequence of clauses (one per line, DIMACS
/// integers terminated by `0`) that a checker like `drat-trim` or
/// `sat-drat-verify` (this repo) can replay against the original CNF
/// to confirm UNSAT.
///
/// Each learned clause from CDCL conflict analysis is RUP-implied by
/// the current clause set (it's a resolvent of original / prior
/// learned clauses), so dumping them in learn-order gives a sound
/// DRAT proof.  We append a final `0` line to denote the empty
/// clause (proof end).
///
/// Construction cost is negligible: the prover already computes
/// each learned clause; we just `writeln!` it.  Verification cost
/// is linear in proof size × BCP work — typically comparable to
/// or faster than the original solve.
///
/// Caveat: if `--preprocess` was on, the lit vars in the learned
/// clauses reference the *preprocessed* CNF, not the input.  The
/// caller (sat.rs) restricts `--emit-drat` to `--no-preprocess` —
/// same caveat as `--emit-cover`.
struct DratWriter {
    writer: io::BufWriter<std::fs::File>,
    /// Count of clauses written, for the header comment / diagnostic.
    clauses_emitted: usize,
}

impl DratWriter {
    fn new(file: std::fs::File) -> Self {
        Self {
            writer: io::BufWriter::new(file),
            clauses_emitted: 0,
        }
    }

    /// Emit one learned clause as a DIMACS line: `<lit1> <lit2> ... 0`.
    ///
    /// **Domain translation**: the matrix-method CDCL controller
    /// works in the *complement-NNF* domain.  A learned Prod with
    /// alts `[a, b, c]` (Lit polarity as-is) represents the F-domain
    /// CNF clause `(¬a ∨ ¬b ∨ ¬c)`.  Reason: the Prod gets added to
    /// the complement NNF (`¬F`) as a new Sum branch, and a fresh
    /// `(a ∧ b ∧ c)` Sum-child of `¬F` is exactly the F-domain clause
    /// `¬(a ∧ b ∧ c) = ¬a ∨ ¬b ∨ ¬c`.
    ///
    /// So we **negate** each lit when formatting: a positive-polarity
    /// alt becomes a negative DIMACS lit and vice versa.  `Lit::var`
    /// is 0-indexed; DIMACS is 1-indexed, so we also offset.
    fn emit_clause(&mut self, clause: &[logic::matrix::Lit]) -> io::Result<()> {
        for lit in clause {
            // Polarity inverted: complement-NNF Prod alt `lit` =
            // F-domain CNF clause lit `¬lit`.
            let dimacs: i32 = (lit.var as i32 + 1) * if lit.neg { 1 } else { -1 };
            write!(self.writer, "{} ", dimacs)?;
        }
        writeln!(self.writer, "0")?;
        self.clauses_emitted += 1;
        Ok(())
    }

    /// Write the empty clause `0` to mark proof end + flush.
    /// Idempotent (callers can finalize once, then drop).
    fn finalize_unsat(&mut self) -> io::Result<()> {
        writeln!(self.writer, "0")?;
        self.writer.flush()
    }

    /// Number of learned clauses emitted so far (excluding the final
    /// `0` terminator).  Used for diagnostic reporting.
    fn clauses_emitted(&self) -> usize { self.clauses_emitted }
}

/// `PbpWriter` — emit a VeriPB-format pseudo-Boolean proof
/// alongside the search.  PB+VeriPB is strictly more expressive than
/// DRAT+drat-trim: cutting-planes (`pol`) steps can express
/// cardinality reasoning that resolution can't handle in polynomial
/// size (PHP-family, RoundRobin-class problems).
///
/// We start by emitting only RUP rules (same expressivity as DRAT),
/// then layer in `pol` rules for cover-pair resolvents — captures the
/// matrix-method's structural cover knowledge in PB form.
///
/// Format: per VeriPB 3.0 grammar.  Header → `f <n>` (sanity check) →
/// `rup <constraint>;` per learned clause → optional `pol`/etc. for
/// matrix-method translations → `output NONE;` → `conclusion UNSAT
/// : -1;` (pointing at the most-recently-derived constraint as the
/// contradiction witness) → `end pseudo-Boolean proof;`.
///
/// DIMACS lit `n` maps to PB literal `x<n>` (positive) or `~x<n>`
/// (negated).  A clause `(l_1 ∨ … ∨ l_k)` becomes the PB constraint
/// `+1 lit_1 +1 lit_2 ... +1 lit_k >= 1 ;`.
struct PbpWriter {
    writer: io::BufWriter<std::fs::File>,
    n_constraints_initial: usize,
    constraints_emitted: usize,
}

impl PbpWriter {
    /// `n_input_constraints` is the number of CNF clauses in the
    /// input — used for the `f <n>` sanity check.
    fn new(file: std::fs::File, n_input_constraints: usize) -> io::Result<Self> {
        let mut w = io::BufWriter::new(file);
        writeln!(w, "pseudo-Boolean proof version 3.0")?;
        writeln!(w, "f {};", n_input_constraints)?;
        Ok(Self {
            writer: w,
            n_constraints_initial: n_input_constraints,
            constraints_emitted: 0,
        })
    }

    /// Emit one learned clause as a `rup` rule.  Domain translation:
    /// the matrix-method controller's learned `alts` are in
    /// complement-NNF domain; we negate each lit (same as DRAT) so
    /// the result is in the original-F domain.  Then format as PB:
    /// `+1 <lit1> +1 <lit2> ... >= 1`.
    fn emit_rup_clause(&mut self, clause: &[logic::matrix::Lit]) -> io::Result<()> {
        write!(self.writer, "rup")?;
        for lit in clause {
            // Domain flip: complement-NNF alt `lit` = F-domain clause
            // lit `¬lit`.  `Lit::var` is 0-indexed; VeriPB uses
            // 1-indexed `x<i>` names.
            let var = lit.var + 1;
            let want_neg = !lit.neg;  // negated relative to alt
            if want_neg {
                write!(self.writer, " +1 ~x{}", var)?;
            } else {
                write!(self.writer, " +1 x{}", var)?;
            }
        }
        writeln!(self.writer, " >= 1 ;")?;
        self.constraints_emitted += 1;
        Ok(())
    }

    /// Finalize for UNSAT: emit `rup >= 1 ;` (empty clause, RUP-implied
    /// iff F + earlier-derived clauses BCP to contradiction), then
    /// the conclusion/end markers pointing at it.
    fn finalize_unsat(&mut self) -> io::Result<()> {
        writeln!(self.writer, "rup >= 1 ;")?;
        self.constraints_emitted += 1;
        writeln!(self.writer, "output NONE;")?;
        writeln!(self.writer, "conclusion UNSAT : -1;")?;
        writeln!(self.writer, "end pseudo-Boolean proof;")?;
        self.writer.flush()
    }

    /// For SAT outcomes: emit a no-op conclusion + flush.  The proof
    /// is not a refutation in this case; emitting `conclusion SAT`
    /// requires the assignment which we don't always have here.
    /// `conclusion NONE` is always valid.
    fn finalize_sat(&mut self) -> io::Result<()> {
        writeln!(self.writer, "output NONE;")?;
        writeln!(self.writer, "conclusion NONE;")?;
        writeln!(self.writer, "end pseudo-Boolean proof;")?;
        self.writer.flush()
    }

    /// Emit a cover-pair resolvent via cutting-planes `pol`:
    /// `pol <id_a> <id_b> + s ;` adds the resolvent of F-clauses
    /// at IDs `id_a` and `id_b`.  The `+` adds them in PB form,
    /// `s` saturates (caps coefficients at 1) — and since the two
    /// clauses contain complementary literals `X` and `¬X`, those
    /// literals cancel out in the sum, leaving the resolution
    /// product.
    ///
    /// VeriPB assigns the result a fresh ConstraintID = IDmax+1.
    /// We don't reference this ID by absolute number — subsequent
    /// rules can use relative IDs (`-1`, `-2`, ...) or symbolic
    /// labels if needed.
    ///
    /// `id_a` and `id_b` are VeriPB ConstraintIDs (1-indexed; the
    /// first input CNF clause gets ID 1).
    fn emit_pol_resolvent(&mut self, id_a: usize, id_b: usize) -> io::Result<()> {
        writeln!(self.writer, "pol {} {} + s ;", id_a, id_b)?;
        self.constraints_emitted += 1;
        Ok(())
    }

    /// Count of learned-clause `rup` lines emitted so far (excluding
    /// the final empty-clause derivation).
    fn constraints_emitted(&self) -> usize { self.constraints_emitted }

    /// Initial constraint count (= number of CNF clauses, for the
    /// `f <n>` line).  Used in the diagnostic summary.
    #[allow(dead_code)]
    fn n_constraints_initial(&self) -> usize { self.n_constraints_initial }
}

/// `preprocessed`: optional preprocessing handle.  When `Some`,
/// the SAT-witness path (`SearchOutcome::Sat`) reconstructs the
/// original-variable assignment by feeding the search's path
/// literals through `pp.reconstruct_sat_assignment` (which negates
/// each lit to take it from complement-direction to SAT-direction,
/// then replays the recon stack to recover any variables eliminated
/// during preprocessing).  When `None`, the legacy direct
/// `path_lits_to_assignment` is used.
///
/// `emit_cover`: optional path to a file that, when set, receives one
/// cert entry per `CoveredPathPrefix` event the search emits.  Only
/// supported by the `cdcl` and `smart` backends (which use the NNF
/// engine with positions tracked); other backends error.
/// Neural warm-start seed (NeuroBack-style), set once from `--initial-phases`.
/// Read by the cdcl/eff controller builders to seed phase saving.  Indexed by
/// 0-based internal var (= DIMACS var − 1); `Some(b)` = predicted phase.
static INITIAL_PHASES: std::sync::OnceLock<Vec<Option<bool>>> = std::sync::OnceLock::new();

/// Parse a phase file (signed DIMACS lits, `0`-terminated, `c` comments) into a
/// per-variable seed: `seed[|L|-1] = Some(L > 0)` (the predicted phase).
///
/// The matrix search runs on the CNF *complement* and maps a path lit back via
/// `asgn[var] = lit.neg` (see `path_lits_to_assignment`), so the complement-lit
/// polarity to prefer-save IS exactly the predicted phase — the De Morgan
/// complement and that `asgn = neg` mapping cancel.  Hence `Some(L > 0)`.
fn load_initial_phases(path: &std::path::Path, nvars: usize)
    -> Result<Vec<Option<bool>>, String>
{
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read --initial-phases {}: {}", path.display(), e))?;
    let mut seed = vec![None; nvars];
    for line in text.lines() {
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') { continue; }
        for tok in t.split_ascii_whitespace() {
            let l: i32 = tok.parse()
                .map_err(|_| format!("bad token in phase file: {:?}", tok))?;
            if l == 0 { continue; }
            let v = l.unsigned_abs() as usize;
            if v >= 1 && v <= nvars { seed[v - 1] = Some(l > 0); }
        }
    }
    Ok(seed)
}

fn matrix_search(
    comp: NNF,
    nvars: usize,
    show_progress: bool,
    backend: MatrixBackend,
    preprocessed: Option<&logic::preprocess::Preprocessed>,
    emit_cover: Option<&std::path::Path>,
    cover_clauses: Option<&[Vec<i32>]>,
    emit_drat: Option<&std::path::Path>,
    emit_pbp: Option<&std::path::Path>,
    n_input_clauses: usize,
    // Wall-clock timeout in seconds; 0 means "no timeout configured"
    // — the progress renderer suppresses the time bar in that case
    // since there's no meaningful denominator.  Not used for actual
    // cancellation (a separate watcher thread in `main` handles that
    // via SIGTERM); purely informational for the time-budget bar.
    timeout_secs: u64,
    // Variance threshold for Sum-child reordering in eff backends.
    // 0.0 = always reorder (legacy).  See `Args::eff_tau`.  No-op
    // for non-eff backends (Smart, Cdcl, GreedyCdcl).
    eff_tau: f64,
    // Visit-order mode override for eff backends: `Some(0)` forces pure
    // EffectiveCount (used when the input is detected as an exactly-one
    // CSP — PHP/RoundRobin-like — where VSIDS-alternating only wastes
    // effort); `None` keeps the default (restart-alternating portfolio,
    // or whatever `EFF_VSIDS` overrides to).  No-op for non-eff backends.
    eff_vsids_override: Option<u8>,
) -> SearchOutcome {
    // log10 of the total path count.  Used by the progress renderer
    // to map "paths classified so far" onto a [0, 1] bar fill in
    // log-space (each tick of the bar = one constant fold-increase in
    // coverage).  Computed in log-space because the literal
    // `path_count()` overflows f64 to ∞ on huge complement NNFs
    // (PHP-n-n, Steiner, RoundRobin) — log-space stays finite up to
    // 10^(10^308), i.e. unbounded for any formula that fits in RAM.
    let log_total_paths = comp.log_path_count();
    let params = Some(PathParams {
        uncovered_path_limit: 1,           // stop after the first witness
        paths_class_limit:    usize::MAX,
        covered_prefix_limit: usize::MAX,
        no_cover:             true,        // pairs with `_uncovered_only`
    });
    // No longer need to keep a separate clone for post-search
    // `lits_on_path(&prod_path)` — the engine emits the literals
    // along the uncovered path directly via `UncoveredPath::lits`,
    // and walking the original NNF post-hoc is *unsound* for the
    // `eff` backend whose `EffectiveCountWrapper::sum_ord` re-orders
    // Sum children (the path indices end up indexing the wrong
    // children, panicking on out-of-bounds or silently picking the
    // wrong lits).

    // The matrix-method DFS in `for_each_path_prefix_ord` recurses
    // through Sum siblings via continuation closures.  On a CNF
    // complement with N clauses, the top-level Sum has N children, so
    // the traversal nests O(N) deep — for industrial inputs (100k+
    // clauses) that easily blows the default 2 MB tokio stack.
    //
    // Bumping `thread_stack_size` to 1 GB on the runtime builder.
    // The matrix-method DFS recurses through Sum siblings via
    // continuation closures — for a 1.5M-clause CNF complement
    // (e.g. goldcrest-and-11) the arena engine's recursion uses
    // about 350 MB of stack, blowing the previous 256 MB ceiling
    // mid-search with a `thread 'tokio-rt-worker' has overflowed
    // its stack / fatal runtime error` abort.  1 GB handles
    // everything we've measured (worst case ~700 MB on the
    // largest competition CNFs we've benchmarked).  Stack is
    // virtual memory — pages aren't committed until touched — so
    // the 1 GB reservation doesn't grow RSS by 1 GB.
    //
    // The proper fix is to rewrite traverse_sum's sibling recursion
    // as an explicit work-stack iteration; that's a deeper refactor
    // for a follow-up.
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
        .thread_stack_size(1024 * 1024 * 1024)
        .build()
        .expect("tokio runtime");

    // `--emit-cover` only meaningful for backends that use the
    // positions-tracked NNF engine (Cdcl, Smart) — the arena and
    // dual-framework variants either don't track positions or run
    // their cover events through internal channels that bypass the
    // file emitter.  Bail with a clear message before launching the
    // runtime to avoid the user thinking they got covers when they
    // didn't.
    if emit_cover.is_some()
        && !matches!(backend, MatrixBackend::Cdcl | MatrixBackend::Smart | MatrixBackend::EffCover)
    {
        eprintln!("c ERROR: --emit-cover only supported with backend cdcl, smart, or \
                   eff_cover (got {}); the other backends use the positions-OFF or arena \
                   engine which doesn't track the positional info the cert format needs",
                  backend.name());
        std::process::exit(2);
    }
    // eff_cover exists for the proof-verify pipeline, where the cover's
    // positions must reference the INPUT CNF (sat-cover-verify checks
    // against the original).  Preprocessing rewrites/renumbers clauses,
    // so require --no-preprocess when emitting a cover from eff_cover.
    if emit_cover.is_some()
        && matches!(backend, MatrixBackend::EffCover)
        && preprocessed.is_some()
    {
        eprintln!("c ERROR: --emit-cover with backend eff_cover requires --no-preprocess \
                   (cover positions must reference the input CNF for sat-cover-verify)");
        std::process::exit(2);
    }
    if emit_drat.is_some() && !matches!(backend, MatrixBackend::Cdcl) {
        eprintln!("c ERROR: --emit-drat only supported with backend cdcl \
                   (got {}); other backends don't produce learned clauses",
                  backend.name());
        std::process::exit(2);
    }
    if emit_drat.is_some() && preprocessed.is_some() {
        eprintln!("c ERROR: --emit-drat with --preprocess not supported: the DRAT \
                   trace would reference preprocessed-CNF variables, not the input \
                   CNF's.  Rerun with --no-preprocess.");
        std::process::exit(2);
    }
    if emit_pbp.is_some() && !matches!(backend, MatrixBackend::Cdcl) {
        eprintln!("c ERROR: --emit-pbp only supported with backend cdcl \
                   (got {}); other backends don't produce learned clauses",
                  backend.name());
        std::process::exit(2);
    }
    if emit_pbp.is_some() && preprocessed.is_some() {
        eprintln!("c ERROR: --emit-pbp with --preprocess not supported: the PB \
                   proof would reference preprocessed-CNF variables, not the input \
                   CNF's.  Rerun with --no-preprocess.");
        std::process::exit(2);
    }

    rt.block_on(async move {
        // Optional cover writer.  Populated by the Cdcl/Smart match
        // arms when `emit_cover` is set; the post-search block flushes
        // it via Arc-drop after `handle.await` so the file lands on
        // disk before the verdict is printed.
        let mut cover_writer_arc: Option<Arc<Mutex<CoverWriter>>> = None;
        // Optional DRAT writer.  Populated by the Cdcl match arm
        // when `emit_drat` is set; flushed in the post-search block
        // with a final `0` (empty clause = proof end) on UNSAT.
        let mut drat_writer_arc: Option<Arc<Mutex<DratWriter>>> = None;
        // Open the DRAT file early (outside the match arm) so we can
        // pass the Arc into the cdcl arm cleanly.
        if let Some(drat_path) = emit_drat {
            let file = match std::fs::File::create(drat_path) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("c ERROR: cannot create drat file {}: {}",
                              drat_path.display(), e);
                    std::process::exit(2);
                }
            };
            drat_writer_arc = Some(Arc::new(Mutex::new(DratWriter::new(file))));
        }
        // Optional PBP (VeriPB pseudo-Boolean proof) writer.  Mirror
        // structure: open early, share via Arc<Mutex>, finalize after
        // search.  Header (`pseudo-Boolean proof v3.0` + `f <n>`)
        // gets written in `PbpWriter::new`.
        let mut pbp_writer_arc: Option<Arc<Mutex<PbpWriter>>> = None;
        if let Some(pbp_path) = emit_pbp {
            let file = match std::fs::File::create(pbp_path) {
                Ok(f) => f,
                Err(e) => {
                    eprintln!("c ERROR: cannot create pbp file {}: {}",
                              pbp_path.display(), e);
                    std::process::exit(2);
                }
            };
            match PbpWriter::new(file, n_input_clauses) {
                Ok(w) => pbp_writer_arc = Some(Arc::new(Mutex::new(w))),
                Err(e) => {
                    eprintln!("c ERROR: pbp header write failed: {}", e);
                    std::process::exit(2);
                }
            }
        }

        // Each match arm clones inputs only if it actually needs them.
        // Earlier versions hoisted `nnf_smart = comp.clone();
        // nnf_cdcl = comp.clone();` to the top of the function "so the
        // borrow checker is happy with the if/else producing the same
        // tuple shape" — but those clones lived for the entire search
        // even when the chosen branch (Eff, Dual) didn't reference
        // them, wasting one full NNF copy per unused arm.  For
        // industrial CNFs (e.g. pj2013_k9, ~250 MB per NNF) this was
        // ~500 MB of dead allocation per process times however many
        // sat processes were running in parallel.
        let (handle, mut rx, cancel) = match backend {
            MatrixBackend::Smart => {
                let nnf_smart = comp.clone();
                let p_smart = params.clone();
                if let Some(cover_path) = emit_cover {
                    // Cover-emitting variant — mirrors the Cdcl arm
                    // below.  Smart uses the same NNF positions-on
                    // engine (`classify_paths`), so plumbing is
                    // identical except for the controller builder.
                    let file = match std::fs::File::create(cover_path) {
                        Ok(f) => f,
                        Err(e) => {
                            eprintln!("c ERROR: cannot create cover file {}: {}",
                                      cover_path.display(), e);
                            std::process::exit(2);
                        }
                    };
                    let clauses_arc = std::sync::Arc::new(
                        cover_clauses.expect("--emit-cover requires cover_clauses").to_vec());
                    let cover_w: Arc<Mutex<CoverWriter>> =
                        Arc::new(Mutex::new(CoverWriter::new(file, clauses_arc)));
                    {
                        let mut cw = cover_w.lock().unwrap();
                        let _ = writeln!(cw.writer, "# sat-cover-verify cert v3");
                        let _ = writeln!(cw.writer, "# source: {} backend=smart preprocess={}",
                                         cover_path.display(),
                                         preprocessed.map(|_| "on").unwrap_or("off"));
                    }
                    let cw_for_search = cover_w.clone();
                    let result = comp.classify_paths(64, move |tx| {
                        let on_class: DynOnClass = Box::new(move |class, hit_limit| {
                            if let PathsClass::Covered(cpp) = &class {
                                let mut cw = cw_for_search.lock().unwrap();
                                cw.maybe_write(cpp).expect("cover file write failed");
                            }
                            tx.blocking_send((class, hit_limit)).is_ok()
                        });
                        SmartController::for_nnf_with_cover(&nnf_smart, p_smart, on_class)
                    });
                    cover_writer_arc = Some(cover_w);
                    result
                } else {
                    comp.classify_paths_uncovered_only(64,
                        move |tx| smart_controller_builder(&nnf_smart, p_smart, tx),
                    )
                }
            }
            MatrixBackend::Cdcl => {
                let nnf_cdcl = comp.clone();
                let p_cdcl = params.clone();
                // Build a combined Send+Sync hook: emits each
                // learned clause to whichever writers are
                // configured (DRAT and/or PBP).  Both writers
                // consume `&[Lit]` and translate to their own
                // format internally.
                let drat_hook: Option<logic::controller::cdcl::DratHook> = {
                    let drat = drat_writer_arc.clone();
                    let pbp = pbp_writer_arc.clone();
                    if drat.is_none() && pbp.is_none() {
                        None
                    } else {
                        let hook: logic::controller::cdcl::DratHook =
                            Arc::new(move |alts: &[Lit]| {
                                if let Some(arc) = &drat {
                                    let mut w = arc.lock().unwrap();
                                    w.emit_clause(alts).expect("drat file write failed");
                                }
                                if let Some(arc) = &pbp {
                                    let mut w = arc.lock().unwrap();
                                    w.emit_rup_clause(alts).expect("pbp file write failed");
                                }
                            });
                        Some(hook)
                    }
                };
                // Decide whether to use the cover-emitting search
                // path: when either --emit-cover (writes cover cert)
                // or --emit-pbp (each cover pair → PB `pol`
                // resolvent) is on.  Both need static cover events
                // to flow through the on_class closure.
                let need_cover_path = emit_cover.is_some() || pbp_writer_arc.is_some();
                if need_cover_path {
                    // Optional CoverWriter (only when --emit-cover is set).
                    let cover_w_opt: Option<Arc<Mutex<CoverWriter>>> = emit_cover
                        .map(|cover_path| {
                            let file = std::fs::File::create(cover_path)
                                .unwrap_or_else(|e| {
                                    eprintln!("c ERROR: cannot create cover file {}: {}",
                                              cover_path.display(), e);
                                    std::process::exit(2);
                                });
                            let clauses_arc = std::sync::Arc::new(
                                cover_clauses
                                    .expect("--emit-cover requires cover_clauses")
                                    .to_vec());
                            let cw: Arc<Mutex<CoverWriter>> =
                                Arc::new(Mutex::new(CoverWriter::new(file, clauses_arc)));
                            {
                                let mut cwl = cw.lock().unwrap();
                                let _ = writeln!(cwl.writer, "# sat-cover-verify cert v3");
                                let _ = writeln!(cwl.writer,
                                    "# source: {} backend=cdcl preprocess={}",
                                    cover_path.display(),
                                    preprocessed.map(|_| "on").unwrap_or("off"));
                            }
                            cw
                        });
                    let cw_for_search   = cover_w_opt.clone();
                    let pbp_for_search  = pbp_writer_arc.clone();
                    let drat_for_search = drat_hook.clone();
                    let result = comp.classify_paths(64, move |tx| {
                        let cw_inner  = cw_for_search.clone();
                        let pbp_inner = pbp_for_search.clone();
                        let on_class: DynOnClass = Box::new(move |class, hit_limit| {
                            if let PathsClass::Covered(cpp) = &class {
                                if let Some(cw) = &cw_inner {
                                    let mut w = cw.lock().unwrap();
                                    w.maybe_write(cpp).expect("cover file write failed");
                                }
                                if let Some(pbp) = &pbp_inner {
                                    // Each cover pair (X@p1, ¬X@p2)
                                    // becomes a `pol id_a id_b + s;`
                                    // rule.  Positions are
                                    // `[clause, lit]` vectors;
                                    // VeriPB's constraint IDs for
                                    // input clauses are 1-indexed in
                                    // load order, so clause_idx c
                                    // maps to ID c+1.  Only valid
                                    // under --no-preprocess (which
                                    // we've already enforced upstream).
                                    let (a, b) = &cpp.cover;
                                    if !a.is_empty() && !b.is_empty() {
                                        let id_a = a[0] + 1;
                                        let id_b = b[0] + 1;
                                        let mut w = pbp.lock().unwrap();
                                        w.emit_pol_resolvent(id_a, id_b)
                                            .expect("pbp file write failed");
                                    }
                                }
                            }
                            tx.blocking_send((class, hit_limit)).is_ok()
                        });
                        let mut ctrl = CdclController::for_nnf_with_cover(&nnf_cdcl, p_cdcl, on_class);
                        if let Some(s) = INITIAL_PHASES.get() { ctrl.set_initial_phases(s); }
                        ctrl.drat_hook = drat_for_search;
                        ctrl
                    });
                    // Stash the cover writer Arc so the post-search
                    // block can flush + write its footer (skipped
                    // when --emit-cover wasn't set).
                    cover_writer_arc = cover_w_opt;
                    result
                } else if drat_hook.is_some() {
                    // DRAT-only (no cover): build the controller
                    // manually so we can install the hook.
                    let drat_for_search = drat_hook;
                    comp.classify_paths_uncovered_only(64, move |tx| {
                        let mut ctrl = cdcl_controller_builder(&nnf_cdcl, p_cdcl, tx);
                        if let Some(s) = INITIAL_PHASES.get() { ctrl.set_initial_phases(s); }
                        ctrl.drat_hook = drat_for_search;
                        ctrl
                    })
                } else {
                    comp.classify_paths_uncovered_only(64, move |tx| {
                        let mut ctrl = cdcl_controller_builder(&nnf_cdcl, p_cdcl, tx);
                        if let Some(s) = INITIAL_PHASES.get() { ctrl.set_initial_phases(s); }
                        ctrl
                    })
                }
            }
            MatrixBackend::Eff | MatrixBackend::Effb => {
                // matrix.eff uses the arena engine: build a
                // compact `NnfArena` from the complement NNF, drop
                // the NNF, then drive an arena-native search via
                // `NnfArena::classify_paths_with_arena`.  See
                // `src/nnf_arena.rs` for the layout (12 B per node
                // vs `enum NNF`'s 32 B) and `doc/`-level discussion
                // for the migration rationale — net ~50 % per
                // process memory savings on big CNF complements.
                //
                // `matrix.effb` is the experimental bubble-up
                // variant: same controller stack but drives the
                // engine through `classify_paths_with_arena_bubble_up`
                // (multi-level back-up on CDCL restart).  See the
                // doc comment on `MatrixBackend::Effb` for the
                // soundness caveat.
                use logic::dual::effective_count::{EffectiveCountIndex, EffectiveCounts};
                use logic::dual::path_effective::EffectiveCountWrapper;
                use logic::nnf_arena::NnfArena;
                let p_eff = Some(PathParams {
                    uncovered_path_limit: 1,
                    paths_class_limit:    usize::MAX,
                    covered_prefix_limit: usize::MAX,
                    // `false` here is harmless in arena mode — the
                    // arena-trait `BacktrackWhenCoveredController`
                    // is in `uncovered_only=true` per
                    // `for_arena_with_cover`, which suppresses
                    // Covered event emission regardless of this
                    // flag.  Kept `false` for symmetry with the
                    // NNF wiring's intent ("cover detection on").
                    no_cover:             false,
                });
                let arena = NnfArena::from_nnf(&comp);
                drop(comp);  // ≈ 250 MB freed before search starts
                let tau = eff_tau;  // capture by value into the builder closure
                let builder = move |arena_ref: &NnfArena, tx: tokio::sync::mpsc::Sender<(PathsClass, bool)>| {
                    let on_class: DynOnClass = Box::new(move |class, hit_limit|
                        tx.blocking_send((class, hit_limit)).is_ok());
                    let mut cdcl = CdclController::for_arena_with_cover(arena_ref, p_eff, on_class);
                    if let Some(s) = INITIAL_PHASES.get() { cdcl.set_initial_phases(s); }
                    let idx = EffectiveCountIndex::build_from_arena(arena_ref);
                    let counts = EffectiveCounts::new(&idx);
                    EffectiveCountWrapper::new_with_tau(cdcl, idx, counts, tau).with_vsids_order(eff_vsids_override)
                };
                if matches!(backend, MatrixBackend::Effb) {
                    arena.classify_paths_with_arena_bubble_up(64, builder)
                } else {
                    arena.classify_paths_with_arena(64, builder)
                }
            }
            MatrixBackend::EffCover => {
                // Eff policy on the cover-emitting NNF single-DFS
                // engine.  Same `EffectiveCountWrapper` (EVOLVE-BLOCK)
                // policy as `Eff`, but wrapped around the cover-emitting
                // `CdclController::for_nnf_with_cover` so it can emit a
                // complete static cover certificate (`emit_static_cover`
                // runs at controller construction, independent of which
                // paths the wrapper's policy visits — so an unsound
                // policy yields an incomplete/failing cert, not a wrong
                // "verified UNSAT").  This is the substrate the
                // proof-gated evolution harness runs on.  The
                // wrapper-over-cover-cdcl composition is the same stack
                // `web_app.rs` runs in production (classify_paths_with_nnf
                // so the EffectiveCountIndex is keyed to the engine's
                // own NNF clone — pointer-identity for the count lookups).
                use logic::dual::effective_count::{EffectiveCountIndex, EffectiveCounts};
                use logic::dual::path_effective::EffectiveCountWrapper;
                let tau = eff_tau;
                if let Some(cover_path) = emit_cover {
                    let file = std::fs::File::create(cover_path)
                        .unwrap_or_else(|e| {
                            eprintln!("c ERROR: cannot create cover file {}: {}",
                                      cover_path.display(), e);
                            std::process::exit(2);
                        });
                    let clauses_arc = std::sync::Arc::new(
                        cover_clauses
                            .expect("--emit-cover requires cover_clauses")
                            .to_vec());
                    let cover_w: Arc<Mutex<CoverWriter>> =
                        Arc::new(Mutex::new(CoverWriter::new(file, clauses_arc)));
                    {
                        let mut cwl = cover_w.lock().unwrap();
                        let _ = writeln!(cwl.writer, "# sat-cover-verify cert v3");
                        let _ = writeln!(cwl.writer,
                            "# source: {} backend=eff_cover preprocess=off",
                            cover_path.display());
                    }
                    let cw_for_search = cover_w.clone();
                    let p_ec = params.clone();
                    let result = comp.classify_paths_with_nnf(64, move |nnf_ref, tx| {
                        let cw_inner = cw_for_search.clone();
                        let on_class: DynOnClass = Box::new(move |class, hit_limit| {
                            if let PathsClass::Covered(cpp) = &class {
                                let mut w = cw_inner.lock().unwrap();
                                w.maybe_write(cpp).expect("cover file write failed");
                            }
                            tx.blocking_send((class, hit_limit)).is_ok()
                        });
                        let mut cdcl = CdclController::for_nnf_with_cover(nnf_ref, p_ec, on_class);
                        if let Some(s) = INITIAL_PHASES.get() { cdcl.set_initial_phases(s); }
                        let idx = EffectiveCountIndex::build(nnf_ref);
                        let counts = EffectiveCounts::new(&idx);
                        EffectiveCountWrapper::new_with_tau(cdcl, idx, counts, tau).with_vsids_order(eff_vsids_override)
                    });
                    cover_writer_arc = Some(cover_w);
                    result
                } else {
                    // Fast metric mode: uncovered-only engine + non-cover
                    // cdcl controller (no static-cover enumeration cost).
                    let p_ec = params.clone();
                    comp.classify_paths_uncovered_only_with_nnf(64, move |nnf_ref, tx| {
                        let on_class: DynOnClass = Box::new(move |class, hit_limit|
                            tx.blocking_send((class, hit_limit)).is_ok());
                        let mut cdcl = CdclController::for_nnf(nnf_ref, p_ec, on_class);
                        if let Some(s) = INITIAL_PHASES.get() { cdcl.set_initial_phases(s); }
                        let idx = EffectiveCountIndex::build(nnf_ref);
                        let counts = EffectiveCounts::new(&idx);
                        EffectiveCountWrapper::new_with_tau(cdcl, idx, counts, tau).with_vsids_order(eff_vsids_override)
                    })
                }
            }
            MatrixBackend::GreedyCdcl
            | MatrixBackend::GreedyEff
            | MatrixBackend::BasicEff
            | MatrixBackend::GreedyEffb
            | MatrixBackend::BasicEffb => {
                spawn_dual_matrix_search(backend, comp.clone(), 64, eff_tau)
            }
        };

        let want_progress = show_progress && io::stderr().is_terminal();
        let _term_guard = if want_progress { Some(TerminalGuard::new()) } else { None };

        let start = Instant::now();
        // Publish a stats-snapshot so the timeout watchdog (and any
        // panic handler) can emit the canonical `c stats ...` line
        // even on abrupt termination paths.  `OnceLock::set` is a
        // no-op after the first set, which is fine — only one search
        // runs per process invocation.
        let _ = STATS_SNAPSHOT.set(StatsSnapshot {
            handle: cancel.clone(),
            log10_total_paths: log_total_paths,
            started: start,
        });
        let progress_task = if want_progress {
            Some(tokio::spawn(matrix_progress_loop(
                cancel.clone(), log_total_paths, timeout_secs, start)))
        } else {
            None
        };

        let mut path_lits: Option<Vec<Lit>> = None;
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
                    print_stats_line();
                    eprintln!("c INTERRUPTED after {:.1}ms", ms);
                    std::process::exit(130);   // 128 + SIGINT
                }
                msg = rx.recv() => match msg {
                    Some((PathsClass::Uncovered(up), _)) => { path_lits = Some(up.lits); break; }
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

        // Print the final `c stats ...` line.  See `print_stats_line`
        // for the format / rationale.  Idempotent with the timeout
        // watchdog's own call so we never get a duplicate stats line.
        print_stats_line();

        // Finalize the cover file (if any): write a footer with the
        // verdict tag and flush.  After this `try_unwrap` the only
        // remaining Arc reference is the worker's on_class closure,
        // which got dropped when `handle.await` returned — so the
        // unwrap should succeed.  If it doesn't (defensive: some
        // future code path keeps a clone alive), we still get the
        // file via the cloned Arc and rely on `Drop` to flush.
        if let Some(arc) = cover_writer_arc.take() {
            // Verdict footer: `# verdict UNSAT|SAT (N vars, M
            // implied pairs)`.  The verdict is informational only —
            // the verifier doesn't trust it.  `finalize()` dumps the
            // accumulated var-grouped cert (v3 format) and writes
            // the footer in one shot, then flushes.
            let verdict = if path_lits.is_some() { "SAT" } else { "UNSAT" };
            match Arc::try_unwrap(arc) {
                Ok(mutex) => {
                    let mut cw = mutex.into_inner().expect("cover writer mutex poisoned");
                    let _ = cw.finalize(verdict);
                    // CoverWriter (with its inner BufWriter+File) goes
                    // out of scope here → Drop flushes + closes.
                }
                Err(arc_still_shared) => {
                    let mut cw = arc_still_shared.lock().unwrap();
                    let _ = cw.finalize(verdict);
                }
            }
        }

        // DRAT finalize: on UNSAT, write a final `0` (empty clause
        // = proof end).  On SAT (search found a model), don't
        // terminate with `0` — the proof file is meaningless for SAT
        // and a stray empty clause would falsely claim UNSAT.
        // In that case we still flush to capture whatever learned
        // clauses leaked out, but a SAT-mode DRAT file isn't a valid
        // proof and downstream tooling should refuse to parse it.
        if let Some(arc) = drat_writer_arc.take() {
            let is_unsat = path_lits.is_none();
            let n_emitted = match Arc::try_unwrap(arc) {
                Ok(mutex) => {
                    let mut dw = mutex.into_inner().expect("drat writer mutex poisoned");
                    if is_unsat {
                        let _ = dw.finalize_unsat();
                    } else {
                        let _ = dw.writer.flush();
                    }
                    dw.clauses_emitted()
                }
                Err(arc_still_shared) => {
                    let mut dw = arc_still_shared.lock().unwrap();
                    if is_unsat {
                        let _ = dw.finalize_unsat();
                    } else {
                        let _ = dw.writer.flush();
                    }
                    dw.clauses_emitted()
                }
            };
            eprintln!("c drat: {} RUP-filtered learned clauses emitted{}",
                      n_emitted,
                      if is_unsat { " + final 0" } else { " (SAT — no proof)" });
        }

        // PBP finalize: mirror DRAT.  On UNSAT, the writer emits a
        // final `rup >= 1 ;` (empty clause) + the conclusion/end
        // markers.  On SAT, just close with `conclusion NONE`.
        if let Some(arc) = pbp_writer_arc.take() {
            let is_unsat = path_lits.is_none();
            let n_emitted = match Arc::try_unwrap(arc) {
                Ok(mutex) => {
                    let mut pw = mutex.into_inner().expect("pbp writer mutex poisoned");
                    if is_unsat {
                        let _ = pw.finalize_unsat();
                    } else {
                        let _ = pw.finalize_sat();
                    }
                    pw.constraints_emitted()
                }
                Err(arc_still_shared) => {
                    let mut pw = arc_still_shared.lock().unwrap();
                    if is_unsat {
                        let _ = pw.finalize_unsat();
                    } else {
                        let _ = pw.finalize_sat();
                    }
                    pw.constraints_emitted()
                }
            };
            eprintln!("c pbp: {} RUP-filtered learned clauses emitted{}",
                      n_emitted,
                      if is_unsat { " + final empty clause" } else { " (SAT)" });
        }

        if let Some(lits) = path_lits {
            let asgn = match preprocessed {
                Some(pp) => {
                    // Build a SAT-direction partial assignment from
                    // the search path (complement-direction lits →
                    // negate to get the assignment that satisfies F).
                    let mut sat_asgn: Vec<Lit> = lits.into_iter()
                        .map(|l| l.complement())
                        .collect();
                    // Pad missing surviving variables with `false`
                    // *before* replaying the reconstruction stack.
                    //
                    // Why this matters: Phase 3/4 BVE recon `Defined`
                    // steps reconstruct an eliminated variable by
                    // evaluating an NNF defn against the surviving
                    // assignment.  If a survivor referenced by the
                    // defn is missing from `sat_asgn`, the defn
                    // evaluation returns `Err(())`, which
                    // `extend_assignment` silently coerces to
                    // `false` via `.unwrap_or(false)`.  Without
                    // pre-padding, the eliminated var's recomputed
                    // value bakes in "missing survivors = false"
                    // implicitly — and the only way for the
                    // resulting full model to be sound is for the
                    // *real* bool_asgn missing-var fill to also be
                    // `false`.  Use `pad_survivors_and_extend`
                    // (the documented safe API) which pads
                    // survivors with `false` explicitly, then
                    // initialise bool_asgn to `false` so the two
                    // agree.  Confirmed sound on Circuit_multiplier24
                    // (26 Defined recon steps, was producing models
                    // that failed 2 of 15 000 clauses before the fix).
                    pp.pad_survivors_and_extend(&mut sat_asgn, nvars as u32);
                    let mut bool_asgn = vec![false; nvars];
                    for l in &sat_asgn {
                        let i = l.var as usize;
                        if i < nvars {
                            // `neg = false` ⇒ x is true ⇒ asgn[i] = true.
                            bool_asgn[i] = !l.neg;
                        }
                    }
                    bool_asgn
                }
                None => {
                    let refs: Vec<&Lit> = lits.iter().collect();
                    path_lits_to_assignment(nvars, &refs)
                }
            };
            SearchOutcome::Sat(asgn)
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
    // Variance-gated Sum-reordering threshold for the eff-wrapped
    // legs of dual backends (GreedyEff, BasicEff, GreedyEffb,
    // BasicEffb).  0.0 = always reorder (legacy).  No-op for
    // GreedyCdcl whose dual path doesn't include eff wrapping.
    eff_tau: f64,
) -> (
    tokio::task::JoinHandle<Result<(), Box<dyn std::error::Error + Send>>>,
    tokio::sync::mpsc::Receiver<(PathsClass, bool)>,
    PathClassificationHandle,
) {
    use logic::dual::{
        solve_dual_with_cancel, BasicCoverController, BasicCoverState,
        CdclDualPathController, EffectivePathController, GreedyMaxCoverController,
        SearchMode,
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
    // CDCL trailing-indicator atoms — see `ProgressAtoms` for why we
    // also publish these.  The progress renderer surfaces them as
    // `conf K rst R` on the path bar.
    let conflicts_atom = cancel.conflicts_atom();
    let restarts_atom  = cancel.restarts_atom();

    let handle = tokio::task::spawn_blocking(move || {
        let _ = match backend {
            MatrixBackend::GreedyCdcl => {
                let cover = GreedyMaxCoverController::default();
                let path  = CdclDualPathController::<BasicCoverState>::with_stream(tx)
                    .with_progress(progress_atom)
                    .with_cdcl_stats(conflicts_atom, restarts_atom);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            MatrixBackend::GreedyEff => {
                let cover = GreedyMaxCoverController::default();
                let path  = EffectivePathController::<BasicCoverState>::with_stream(tx)
                    .with_progress(progress_atom)
                    .with_cdcl_stats(conflicts_atom, restarts_atom)
                    .with_eff_tau(eff_tau);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            MatrixBackend::BasicEff => {
                // BasicCoverController doesn't pre-mine — A only
                // consumes pairs B emits.  Useful on big CNFs where
                // GreedyMaxCoverController's `mine_pairs(nnf)` cost
                // (O(N² × max_arity²) clause-pair comparisons)
                // dominates the actual matrix-method search.
                let cover = BasicCoverController::default();
                let path  = EffectivePathController::<BasicCoverState>::with_stream(tx)
                    .with_progress(progress_atom)
                    .with_cdcl_stats(conflicts_atom, restarts_atom)
                    .with_eff_tau(eff_tau);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            MatrixBackend::GreedyEffb => {
                // Bubble-up variant of greedy×eff — see
                // `MatrixBackend::Effb` doc for the soundness caveat.
                let cover = GreedyMaxCoverController::default();
                let path  = EffectivePathController::<BasicCoverState>::with_stream(tx)
                    .with_progress(progress_atom)
                    .with_cdcl_stats(conflicts_atom, restarts_atom)
                    .with_bubble_up()
                    .with_eff_tau(eff_tau);
                solve_dual_with_cancel(
                    &target_nnf, cover, path, SearchMode::Satisfiable,
                    external_cancel,
                )
            }
            MatrixBackend::BasicEffb => {
                // Bubble-up variant of basic×eff — see
                // `MatrixBackend::Effb` doc for the soundness caveat.
                let cover = BasicCoverController::default();
                let path  = EffectivePathController::<BasicCoverState>::with_stream(tx)
                    .with_progress(progress_atom)
                    .with_cdcl_stats(conflicts_atom, restarts_atom)
                    .with_bubble_up()
                    .with_eff_tau(eff_tau);
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

/// Tokio task that re-renders the matrix-search progress display every
/// 100ms until the search completes or the task is aborted.  Reads
/// `paths_so_far` off the `PathClassificationHandle` (published every
/// 4096 traversal steps by the wrapping
/// [`logic::controller::CancelController`]).
///
/// `log_total` is `log10(total_path_count)` — see `NNF::log_path_count`
/// for why we work in log-space (literal counts overflow f64 on huge
/// formulas).  `timeout_secs == 0` suppresses the time-budget bar.
async fn matrix_progress_loop(
    cancel: PathClassificationHandle,
    log_total: f64,
    timeout_secs: u64,
    start: Instant,
) {
    let mut interval = tokio::time::interval(Duration::from_millis(100));
    interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
    // Skip the first immediate tick so we don't render before any work
    // has happened (the first non-zero update arrives ~ms in).
    interval.tick().await;
    let mut frame: u64 = 0;
    // **Furthest-progress high-water mark.**  The eff backend's
    // `pruned_paths_current` shrinks on backtrack (each pop reverses
    // the per-push credit) and on CDCL restart (all pops at once),
    // so `so_far` can drop between renders.  We mirror the wrapper's
    // own `pruned_paths_peak` here at the render layer — tracking
    // the max `so_far` ever observed — and pass it to the renderer,
    // which draws a `▏` indicator at that position.  Gives the user
    // a visual reference for "best progress in any single attempt"
    // alongside "current progress in this attempt."  Strictly
    // monotone-non-decreasing.
    let mut max_so_far: f64 = 0.0;
    loop {
        interval.tick().await;
        let so_far = cancel.paths_so_far();
        if so_far > max_so_far { max_so_far = so_far; }
        let elapsed = start.elapsed().as_secs_f64();
        // CDCL trailing-indicator stats — `conf` (conflicts learned)
        // and `rst` (restarts).  Always read; render skips them when
        // both are zero (i.e. non-CDCL backend).
        let conflicts = cancel.conflicts_so_far();
        let restarts  = cancel.restarts_so_far();
        render_progress(so_far, max_so_far, log_total, elapsed, timeout_secs, frame,
                        conflicts, restarts);
        frame = frame.wrapping_add(1);
    }
}

/// Render the progress display: a log-scale path bar plus (when a
/// timeout is configured) a wall-clock time bar stacked below it.
///
/// **Why two bars.**  The path bar uses log-space so it actually
/// moves on hard instances: a literal `so_far/total` would sit at 0%
/// for hours then jump to 100%, because path counts grow
/// exponentially while observed coverage starts near zero.  In
/// log-space the bar advances at roughly constant rate as the search
/// chews through orders of magnitude — but that means "50% on the bar"
/// means "covered √total paths", not "halfway done in real terms."
/// The time bar gives the honest ETA-style signal that the log bar
/// can't.  Combined they answer: "am I making progress" (log bar) and
/// "am I about to time out" (time bar) without either lying.
///
/// **Frame `0`** prints both lines fresh.  Subsequent frames cursor-up
/// once and overwrite both lines in place.  The cursor invariant is:
/// after every render, the cursor sits at the end of the *second*
/// (time) line — or the first (path) line if there's no time bar.
/// `restore_terminal()` knows about both lines and clears them on
/// exit.
fn render_progress(
    so_far: f64,
    max_so_far: f64,
    log_total: f64,
    elapsed_secs: f64,
    timeout_secs: u64,
    frame: u64,
    conflicts: usize,
    restarts: usize,
) {
    let bar_width = 30usize;

    // ─── Line 1: log-space path-progress bar ────────────────────
    // so_far == 0  →  log10 is -inf  →  indeterminate-mode slider.
    // log_total <= 0  →  formula has ≤ 1 path  →  also indeterminate
    // (a one-tick search isn't worth a progress bar anyway).
    let log_so_far = if so_far > 0.0 { so_far.log10() } else { f64::NEG_INFINITY };
    let have_log_total = log_total.is_finite() && log_total > 0.0;
    let have_log_progress = log_so_far.is_finite() && have_log_total;

    let line1_bar = if have_log_progress {
        let frac = (log_so_far / log_total).clamp(0.0, 1.0);
        let filled = ((frac * bar_width as f64).round() as usize).min(bar_width);
        // High-water mark cell.  `max_so_far` is monotone-non-decreasing
        // (tracked outside the renderer); it advances as `so_far` hits
        // new peaks and STAYS PUT when the eff backend's restart resets
        // `pruned_paths`, so the user can see "best ever" alongside
        // "current".  Position: the rightmost cell that would be filled
        // at the peak.  Hidden when current ≥ peak (no mark to show).
        let log_peak = if max_so_far > 0.0 { max_so_far.log10() } else { f64::NEG_INFINITY };
        let peak_filled = if log_peak.is_finite() {
            let pf = (log_peak / log_total).clamp(0.0, 1.0);
            ((pf * bar_width as f64).round() as usize).min(bar_width)
        } else {
            0
        };
        let marker_pos: Option<usize> = if peak_filled > filled && peak_filled > 0 {
            Some(peak_filled - 1)
        } else {
            None
        };
        (0..bar_width)
            .map(|i| {
                if i < filled                { '█' }
                else if Some(i) == marker_pos { '▏' }
                else                          { '·' }
            })
            .collect::<String>()
    } else {
        // Indeterminate slider: ◉ advances 1 cell per frame (10/s).
        let pos = (frame as usize) % bar_width;
        (0..bar_width)
            .map(|i| if i == pos { '◉' } else { '·' })
            .collect::<String>()
    };

    let rate = if elapsed_secs > 0.0 { so_far / elapsed_secs } else { 0.0 };
    // CDCL trailing-indicator stats.  Suppress the `conf`/`rst`
    // fragment entirely on non-CDCL backends (both atoms still at 0)
    // so the line stays compact and the TUI display doesn't get
    // misleading "conf 0" badges.  When non-zero, append them after
    // the path total so the eye sees: bar → coverage → work-done.
    // Tight spacing (single-space separators, no double-space) to
    // maximize visibility in the multi-worker TUI grid where each
    // worker row is truncated to `terminal_cols - name_prefix - 1`.
    // The wider double-space style was eating ~3 chars of right-side
    // visibility (the rate / time tokens were the first to get cut).
    let cdcl_frag = if conflicts > 0 || restarts > 0 {
        format!(" conf {} rst {}", format_count(conflicts as f64), restarts)
    } else {
        String::new()
    };
    let line1 = format!(
        "c [{}] paths {} / {}{}  ({}/s)  {:.1}s",
        line1_bar,
        format_count(so_far),
        format_log_count(log_total),
        cdcl_frag,
        format_count(rate),
        elapsed_secs,
    );

    // ─── Line 2: wall-clock time-budget bar (only when configured) ──
    let line2 = if timeout_secs > 0 {
        let frac = (elapsed_secs / timeout_secs as f64).clamp(0.0, 1.0);
        let filled = ((frac * bar_width as f64).round() as usize).min(bar_width);
        let bar: String = (0..bar_width)
            .map(|i| if i < filled { '█' } else { '·' })
            .collect();
        Some(format!(
            "c [{}] time  {:.1}s / {}s",
            bar, elapsed_secs, timeout_secs,
        ))
    } else {
        None
    };

    // ─── Write to stderr.  On frame > 0 cursor-up to overwrite line1
    // in place; \r\x1b[2K on each line clears and reprints.
    let n_lines: u16 = if line2.is_some() { 2 } else { 1 };
    if frame > 0 && n_lines > 1 {
        eprint!("\x1b[{}A", n_lines - 1);
    }
    eprint!("\r\x1b[2K{}", line1);
    if let Some(l2) = &line2 {
        eprint!("\n\r\x1b[2K{}", l2);
    }
    let _ = io::stderr().flush();
    // Publish to restore_terminal() so it knows how many lines to
    // clear when the search finishes / panics / receives a signal.
    PROGRESS_LINES_DRAWN.store(n_lines as u8, Ordering::Relaxed);
}

/// Format a log10-valued count for display.  Small values (< 10⁹) are
/// reconstructed back into K/M/G form so they look like normal counts;
/// large values are shown as `10^x.y` since the actual integer would
/// be unprintable.  `-inf` → "0" (formula has no paths at all).
fn format_log_count(log10_n: f64) -> String {
    if !log10_n.is_finite() {
        return if log10_n < 0.0 { "0".into() } else { "?".into() };
    }
    if log10_n < 9.0 {
        // Round-trip back to a literal count for compact display.
        // `format_count` handles K/M/G prefixes for us.
        format_count(10f64.powf(log10_n))
    } else {
        format!("10^{:.1}", log10_n)
    }
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

/// Number of progress lines the renderer last drew (0 = nothing
/// drawn yet; 1 = path bar only; 2 = path bar + time bar).  Read by
/// `restore_terminal` to know how many lines to clear without
/// clobbering legitimate scrollback above the progress block.
/// `AtomicU8` because it's loaded/stored from signal handlers, which
/// need lock-free access.
static PROGRESS_LINES_DRAWN: AtomicU8 = AtomicU8::new(0);

/// Shared snapshot of the currently-running search's stats handle +
/// total-paths log10 + search start time.  Registered by
/// `matrix_search` / `cadical_search` once their internal state is
/// set up; read by the timeout watchdog (which calls
/// `std::process::exit(124)` and would otherwise lose the final
/// stats line) and by panic handlers.  `OnceLock` because exactly one
/// search runs per process invocation.
static STATS_SNAPSHOT: std::sync::OnceLock<StatsSnapshot> = std::sync::OnceLock::new();

struct StatsSnapshot {
    handle: PathClassificationHandle,
    log10_total_paths: f64,
    started: Instant,
}

/// Print the canonical `c stats ...` line on stderr.  Idempotent: a
/// "printed" flag ensures we only emit one stats line per process
/// run even if both the watchdog and the normal-completion path fire
/// (e.g. a SAT result that lands microseconds before the timeout
/// watchdog wakes).  Safe to call from any thread.
fn print_stats_line() {
    static PRINTED: AtomicBool = AtomicBool::new(false);
    if PRINTED.swap(true, Ordering::SeqCst) {
        return;
    }
    let Some(s) = STATS_SNAPSHOT.get() else { return; };
    let elapsed_ms = s.started.elapsed().as_secs_f64() * 1000.0;
    eprintln!(
        "c stats paths={:.6e} log10_total_paths={:.4} conflicts={} restarts={} elapsed_ms={:.3}",
        s.handle.paths_so_far(),
        s.log10_total_paths,
        s.handle.conflicts_so_far(),
        s.handle.restarts_so_far(),
        elapsed_ms,
    );
}

/// Write the cursor-restore + clear-line escape bytes via the raw
/// `write` syscall.  Async-signal-safe and panic-safe — fine to
/// call from signal handlers, panic hooks, and `Drop`.
fn restore_terminal() {
    // Clear whatever progress lines we drew.  The cursor sits at the
    // end of the *last* line drawn (line 2 if there was a time bar,
    // else line 1).  For the 2-line case we clear line 2, cursor-up,
    // clear line 1; for the 1-line case we just clear line 1.
    // Always re-show the cursor.
    //
    // We can't use `eprint!` here — this is called from signal
    // handlers, so we go through the raw `write(2)` syscall on a
    // 'static byte buffer.
    let lines = PROGRESS_LINES_DRAWN.load(Ordering::Relaxed);
    const TWO_LINES:  &[u8] = b"\r\x1b[2K\x1b[1A\r\x1b[2K\x1b[?25h";
    const ONE_LINE:   &[u8] = b"\r\x1b[2K\x1b[?25h";
    const JUST_SHOW:  &[u8] = b"\x1b[?25h";
    let bytes: &[u8] = match lines {
        0 => JUST_SHOW,
        1 => ONE_LINE,
        _ => TWO_LINES,
    };
    // SAFETY: `write(2)` is async-signal-safe.  fd 2 is stderr.  The
    // buffer is a 'static slice so it's always valid.  We ignore the
    // return value because there's nothing useful to do if it fails
    // (we're typically on the way out anyway).
    unsafe {
        let _ = libc::write(
            libc::STDERR_FILENO,
            bytes.as_ptr() as *const libc::c_void,
            bytes.len(),
        );
    }
    // Mark as cleared so a subsequent restore_terminal call (e.g. the
    // panic hook firing after the SIGINT handler already ran) doesn't
    // clear additional lines that didn't belong to us.
    PROGRESS_LINES_DRAWN.store(0, Ordering::Relaxed);
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

/// Print the SAT-competition `v` line(s) for the given assignment.
/// `asgn[i]` is the truth value of variable `i + 1` (1-based DIMACS):
/// `true` writes `+i`, `false` writes `-i`.  The final value line is
/// terminated by the literal `0` per the SAT-competition spec.
///
/// **Line length**: the SAT-competition rules cap each value line at
/// 4096 characters.  For inputs with more than ~680 variables, a
/// single all-on-one-line emission would overflow that limit, so this
/// writer splits the assignment across multiple `v ` lines, each kept
/// safely under 4096 chars (including the trailing newline).  Only
/// the last line carries the `0` terminator.
fn write_v_line<W: io::Write>(w: &mut W, asgn: &[bool]) -> io::Result<()> {
    // Leave headroom so that the final ` 0\n` always fits on whatever
    // line we're on without re-checking the limit twice.  An int32
    // literal is at most 11 chars including the sign, so the per-lit
    // worst case is " <11-digit-lit>" = 12 chars — 4090 gives us
    // ample room for both that and the eventual ` 0\n` tail.
    const MAX_LINE: usize = 4090;
    let mut line = String::from("v");
    for (i, &val) in asgn.iter().enumerate() {
        let v = (i + 1) as i32;
        let lit = if val { v } else { -v };
        let lit_str = lit.to_string();
        // +1 for the leading space.  If the lit won't fit, flush the
        // current line (no terminator yet — it's not the last) and
        // start a fresh `v ` line.
        if line.len() + 1 + lit_str.len() > MAX_LINE {
            writeln!(w, "{}", line)?;
            line.clear();
            line.push('v');
        }
        line.push(' ');
        line.push_str(&lit_str);
    }
    // Final line: append the ` 0` terminator and flush.  If the
    // current line is too long for the terminator (rare — only when
    // the last literal pushed it right up to the limit), wrap once
    // more onto a fresh line.
    if line.len() + 2 > MAX_LINE {
        writeln!(w, "{}", line)?;
        line.clear();
        line.push('v');
    }
    line.push_str(" 0");
    writeln!(w, "{}", line)
}

/// What kind of search to run.  Either a `MatrixBackend` (the
/// matrix-method path-search variants) or CaDiCaL (the bundled
/// reference SAT solver).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum BackendChoice {
    Matrix(MatrixBackend),
    Cadical,
    /// Verified portfolio: first try the standalone Cook PB-prover (a
    /// structure pattern-match → polynomial VeriPB PB proof for PHP /
    /// RoundRobin / MVRoundRobin / clique-coloring / mutilated-chessboard),
    /// and if no shape is detected, run the CaDiCaL binary with `--lrat` so
    /// its clausal reasoning is emitted as native LRAT, checkable by the
    /// fast formally-verified cake_lpr.  Either way a solved UNSAT comes
    /// with a machine-checkable certificate (path via `--proof`; format
    /// announced as `c pb-cadical: proof-format=pbp|lrat`).  Short-circuits
    /// before the matrix search.
    PbCadical,
    /// Hydra: the structure-dispatch portfolio — pb-cadical plus an
    /// XOR/parity stage between the Cook prover and CaDiCaL.  Stages:
    /// (1) Cook shape → polynomial VeriPB PB proof; (2) XOR recovery +
    /// GF(2) Gaussian elimination → decides pure-parity formulas outright
    /// (SAT with a checkable witness; UNSAT currently uncertified) and
    /// simplifies mixed formulas via GE-forced units; (3) residual →
    /// CaDiCaL with native LRAT (cake_lpr-checkable).  Every stage's
    /// verdict is sound; certificates per stage (`proof-format=pbp|lrat|
    /// none`).
    Hydra,
    /// Hydra plus the symmetry-breaking stage (`logic::symbreak`)
    /// between the Cook/XOR preprocessing and the CaDiCaL handoff.
    /// Detects the formula's automorphisms and adds lex-leader SBP
    /// clauses. SAT verdicts stay sound + certified-by-witness; a
    /// symmetry-broken UNSAT is sound but UNCERTIFIED (no LRAT — the
    /// augmented formula's proof does not certify the original), so
    /// this variant trades some UNSAT-proof coverage for potential
    /// speed on symmetric instances that escape the Cook shapes.
    HydraSymBreak,
    /// Hydra whose no-Cook-shape fall-through is the SAT Competition
    /// 2026 main-track winner satsuma-iter+kissat (M. Anders et al.),
    /// run via the local `satsuma-iter-kissat` Docker image (build:
    /// tools/satsuma/build.sh). satsuma breaks symmetries and emits a
    /// binary-SR proof of the breaking; kissat appends its refutation;
    /// dsr-trim (in-container) verifies the COMPOSED proof against the
    /// ORIGINAL formula — certified UNSAT even when symmetries fired.
    HydraSatsuma,
    /// Bare satsuma-iter+kissat (the SAT Competition 2026 main-track
    /// winner) with NO hydra preprocessing — no Cook shapes, no XOR/GE:
    /// the raw formula goes straight to the Docker pipeline. The
    /// baseline arm for A/B against `hydra_satsuma` (which adds hydra's
    /// stages in front) on identical hardware.
    Satsuma,
}

impl BackendChoice {
    fn name(self) -> &'static str {
        match self {
            BackendChoice::Matrix(m) => m.name(),
            BackendChoice::Cadical   => "cadical",
            BackendChoice::PbCadical => "pb-cadical",
            BackendChoice::Hydra     => "hydra",
            BackendChoice::HydraSymBreak => "hydra_sym_break",
            BackendChoice::HydraSatsuma  => "hydra_satsuma",
            BackendChoice::Satsuma       => "satsuma",
        }
    }

    /// Parse a `--backend NAME` argument value.  Accepts the canonical
    /// names from the bench/UI (`smart`, `cdcl`, `eff`, `greedy_cdcl`,
    /// `greedy_eff`, `cadical`) plus a few aliases for convenience.
    ///
    /// The `*b` suffix selects the experimental bubble-up variant of
    /// the corresponding backend (`effb`, `basic_effb`, `greedy_effb`)
    /// — same controller stack, but the engine propagates CDCL's
    /// `Some(usize::MAX)` restart signal up through Prod/Sum frames
    /// instead of exhausting each sibling.  Faster per restart cycle
    /// but has a known wrong-UNSAT mode; verify results against a
    /// trusted backend before trusting any UNSAT.
    fn parse(s: &str) -> Result<Self, String> {
        match s {
            "smart"      | "matrix.smart"  => Ok(BackendChoice::Matrix(MatrixBackend::Smart)),
            "cdcl"       | "matrix.cdcl"   => Ok(BackendChoice::Matrix(MatrixBackend::Cdcl)),
            "eff"        | "matrix.eff"    => Ok(BackendChoice::Matrix(MatrixBackend::Eff)),
            "eff_cover"  | "eff-cover"
                         | "matrix.eff_cover" => Ok(BackendChoice::Matrix(MatrixBackend::EffCover)),
            "effb"       | "matrix.effb"   => Ok(BackendChoice::Matrix(MatrixBackend::Effb)),
            "greedy_cdcl" | "greedy×cdcl"
                         | "greedyxcdcl"   => Ok(BackendChoice::Matrix(MatrixBackend::GreedyCdcl)),
            "greedy_eff" | "greedy×eff"
                         | "greedyxeff"    => Ok(BackendChoice::Matrix(MatrixBackend::GreedyEff)),
            "greedy_effb" | "greedy×effb"
                         | "greedyxeffb"   => Ok(BackendChoice::Matrix(MatrixBackend::GreedyEffb)),
            "basic_eff"  | "basic×eff"
                         | "basicxeff"     => Ok(BackendChoice::Matrix(MatrixBackend::BasicEff)),
            "basic_effb" | "basic×effb"
                         | "basicxeffb"    => Ok(BackendChoice::Matrix(MatrixBackend::BasicEffb)),
            "cadical"                      => Ok(BackendChoice::Cadical),
            "pb-cadical" | "pb_cadical"
                         | "pbcadical"      => Ok(BackendChoice::PbCadical),
            "hydra"                        => Ok(BackendChoice::Hydra),
            "hydra_sym_break" | "hydra-sym-break"
                         | "hydrasymbreak"  => Ok(BackendChoice::HydraSymBreak),
            "hydra_satsuma" | "hydra-satsuma"
                         | "hydrasatsuma"   => Ok(BackendChoice::HydraSatsuma),
            "satsuma"                      => Ok(BackendChoice::Satsuma),
            _ => Err(format!(
                "unknown backend {:?}; expected one of: smart, cdcl, eff, eff_cover, effb, \
                 greedy_cdcl, greedy_eff, greedy_effb, basic_eff, basic_effb, cadical, \
                 pb-cadical, hydra, hydra_sym_break, hydra_satsuma, satsuma", s
            )),
        }
    }
}

/// Parsed command-line flags.
struct Args {
    show_progress: bool,
    backend:       BackendChoice,
    /// Hard wall-clock limit in seconds.  When the search runs longer
    /// than this, the binary prints `c TIMEOUT after Ns` and exits
    /// with status 124 (the GNU `timeout` exit code for "command
    /// timed out").  Default 6000 s; pass `--timeout 0` to disable.
    timeout_secs:  u64,
    /// Run NNF-level preprocessing (top-level unit propagation, BVE,
    /// normalisation) before handing the formula to the matrix-method
    /// search.  Always disabled for the cadical backend (it has its
    /// own internal preprocessor).  Default `true`.
    preprocess:    bool,
    /// Maximum input clause count for which `--preprocess` actually
    /// runs.  Preprocessing costs ~150 µs/clause, so on very large
    /// inputs it can burn the whole time budget before the search even
    /// starts; above this cap preprocess is auto-skipped (with a
    /// `c preprocess: auto-skipped …` note).  Default 250_000.  Set to
    /// `0` for NO cap (preprocess regardless of size — only sensible
    /// with a very large `--timeout`).  Override with
    /// `--preprocess-max-clauses N`; drivable through
    /// `run_benchmark.py --sat-arg`.
    preprocess_max_clauses: usize,
    /// XOR-recovery + GF(2) Gaussian-elimination pre-pass (matrix
    /// backends only).  On by default; disable with `--no-xor-gauss`.
    /// Decides pure-parity formulas (random mod-2 systems, Urquhart,
    /// the x1/x2 family) in polynomial time, which resolution — and the
    /// matrix search — can't.
    xor_gauss: bool,
    /// Symmetry-breaking pre-CaDiCaL stage (hydra only): detect the
    /// formula's automorphisms (`logic::symbreak`, a dejavu-lineage IR
    /// search) and add lex-leader SBP clauses before the handoff. SAT
    /// verdicts + witnesses stay sound (SBPs are sat-preserving; the
    /// model is projected back to the original variables); UNSAT is
    /// sound but uncertified until the SR/VeriPB symmetry proof (Phase
    /// 6). None = default (on for `hydra_sym_break`, off for `hydra`);
    /// `--symbreak`/`--no-symbreak` force it either way.
    symbreak: Option<bool>,
    /// hydra_satsuma/satsuma: wall-clock budget (seconds) for the
    /// in-container dsr-trim verification of an UNSAT's composed SR
    /// proof. Runs AFTER the verdict is printed (never eats solve
    /// budget; the watchdog stands down once the verdict lands). On
    /// timeout the UNSAT stays sound but is recorded UNCERTIFIED.
    /// Default 600; 0 = unlimited.
    satsuma_verify_secs: u64,
    /// hydra_satsuma/satsuma: per-container hard memory cap in GiB
    /// (docker --memory/--memory-swap). 0 = uncapped (competition-
    /// faithful; the Docker VM's total allocation still binds). A
    /// capped container that OOMs fails only that instance, recorded
    /// as TIMEOUT/unknown rather than destabilizing neighbors.
    satsuma_mem_gb: u64,
    /// Run the Cook PB-prover shape detector (hydra/pb-cadical). Default
    /// `true`; `--no-cook` disables it (isolates later stages for A/B).
    cook: bool,
    /// Skip the XOR-GE pass when the input has more than this many
    /// clauses (0 = no cap).  Like `preprocess_max_clauses`, this guards
    /// against the recovery pass — which groups every clause by its
    /// variable set — eating the whole time budget on giant inputs
    /// (e.g. GP_216_290_40: 25M clauses) before the search ever starts.
    /// XOR structure worth recovering lives in small/structured formulas
    /// (parity, ezfact: thousands of clauses), so a generous cap loses
    /// nothing real.  Default 1,000,000.
    xor_gauss_max_clauses: usize,
    /// Optional cover-certificate output path.  When set, every
    /// `CoveredPathPrefix` event from the matrix-method search gets
    /// written to this file, producing a UNSAT certificate that
    /// `sat-cover-verify` can replay against the original CNF.  Only
    /// supported by the `cdcl` and `smart` backends.
    emit_cover:    Option<std::path::PathBuf>,
    /// Optional DRAT-proof output path.  When set, every CDCL
    /// learned clause is dumped to the file in DIMACS DRAT format
    /// (`<lit1> <lit2> ... 0` per line), terminated by `0` (empty
    /// clause = proof end).  Validate with `sat-drat-verify <cnf>
    /// <FILE>` or any standard DRAT checker (drat-trim).  Only
    /// supported by the `cdcl` backend (the only one producing
    /// learned clauses).
    emit_drat:     Option<std::path::PathBuf>,
    /// Optional pseudo-Boolean proof (VeriPB .pbp format) output
    /// path.  Each pure-resolution learned clause is emitted as a
    /// `rup` rule; the proof ends with `rup >= 1 ;` (empty clause)
    /// + `conclusion UNSAT` for refutation.  Verify with
    /// `veripb --cnf <cnf> <FILE>`.  Only supported by `cdcl` +
    /// `--no-preprocess`, same as `--emit-drat`.
    emit_pbp:      Option<std::path::PathBuf>,
    /// Optional Cook-style polynomial PB proof output path.  When set,
    /// inspect the input CNF for known cardinality shapes (PHP-N-M,
    /// RoundRobin n_d).  On match, emit a polynomial-size VeriPB proof
    /// using Cook's extension-variable construction + the
    /// at-most-1-from-pairwise-mutex subroutine — see
    /// `doc/cook_php_walkthrough.md`.  No solver search is run; the
    /// proof is generated directly from the structure analysis.
    /// On no-match, exits with a non-zero code and a clear error
    /// (use `--emit-pbp` for unstructured CNFs).
    emit_cook_pbp: Option<std::path::PathBuf>,
    /// Proof output path for the `pb-cadical` backend.  On an UNSAT verdict
    /// the proof is written here: the Cook path emits a VeriPB PB proof
    /// (`veripb <cnf> <FILE>`), the CaDiCaL path emits native LRAT
    /// (`cake_lpr <cnf> <FILE>`).  The chosen format is announced on stderr
    /// as `c pb-cadical: proof-format=pbp|lrat`.  Optional: without it,
    /// `pb-cadical` still solves and prints the verdict but writes no proof.
    proof: Option<std::path::PathBuf>,
    /// CDCL engine for the pb-cadical / hydra final stage: "cadical"
    /// (default; native LRAT) or "kissat" (binary DRAT, elaborated to LRAT
    /// via `drat-trim -L` when a proof is requested).
    engine: String,
    /// Wall-clock cap (seconds) for the gratgen DRAT->GRAT elaboration.
    /// 0 (default) means "the same as --timeout" — elaboration gets its own
    /// fresh budget equal to the solve budget, mirroring how competitions
    /// budget proof checking separately from solving.  On breach gratgen
    /// is killed and the solve stands without a proof.
    elab_time_s: u64,
    /// Resident-memory cap (MB) for the gratgen DRAT->GRAT elaboration —
    /// gratgen holds the proof + watch structures in RAM, and more with more
    /// threads.  On breach it is killed and the solve stands without a proof.
    /// Default 49152 (48 GB); 0 disables.  (A 30 GB-capped competition node
    /// should lower --elab-jobs to keep the peak under the limit.)
    elab_mem_mb: u64,
    /// Worker threads for gratgen (`-j`).  More threads elaborate faster but
    /// raise peak memory (the proof's clause DB is shared, watch state is
    /// per-thread).  Default 8.
    elab_jobs: u64,
    /// Neural warm-start (NeuroBack-style): a phase file (signed DIMACS lits,
    /// `0`-terminated) of predicted per-variable phases, seeded into the
    /// cdcl/eff phase-saving array (one query before search).  Requires
    /// `--no-preprocess` so seed indices match the input CNF's variables.
    /// Sound by construction — phase saving is a decision tiebreaker only.
    initial_phases: Option<std::path::PathBuf>,
    /// Variance-gated Sum-reordering threshold for Effective-wrapped
    /// backends (`eff`, `effb`, `greedy_eff`, `basic_eff`,
    /// `greedy_effb`, `basic_effb`).  The wrapper applies its
    /// ascending-by-effective-count reordering only when a Sum's
    /// children's effective counts span at least `10^τ` (i.e.
    /// `log10(max/min) >= τ`).  Default 0.0 = always reorder
    /// (preserves the legacy behavior).  Higher values progressively
    /// suppress reordering on uniform-cost formulas where eff's
    /// metric is uninformative and reordering disrupts CDCL's VSIDS
    /// heuristic for no gain (Steiner, PHP-like, random 3-SAT).
    /// `inf` disables Sum reordering entirely (only the sound Prod
    /// zero-count filter remains).  Doesn't affect non-eff backends.
    eff_tau: f64,
}

const DEFAULT_TIMEOUT_SECS: u64 = 6000;
/// Default cap on input clauses for which `--preprocess` runs.
/// Preprocess is ~150 µs/clause, so 250k ≈ 38 s — an acceptable slice
/// of a long budget but a clear "too long" for short benchmarking.
/// Override per-run with `--preprocess-max-clauses N` (0 = no cap).
const DEFAULT_PREPROCESS_MAX_CLAUSES: usize = 250_000;

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        show_progress: false,
        backend: BackendChoice::Matrix(MatrixBackend::Eff),
        timeout_secs: DEFAULT_TIMEOUT_SECS,
        preprocess: true,
        preprocess_max_clauses: DEFAULT_PREPROCESS_MAX_CLAUSES,
        xor_gauss: true,
        symbreak: None,
        satsuma_verify_secs: 600,
        satsuma_mem_gb: 0,
        cook: true,
        xor_gauss_max_clauses: 1_000_000,
        emit_cover: None,
        emit_drat: None,
        emit_pbp: None,
        emit_cook_pbp: None,
        proof: None,
        engine: "cadical".into(),
        elab_time_s: 0,
        elab_mem_mb: 49152,
        elab_jobs: 8,
        initial_phases: None,
        // 0.0 = always reorder (legacy behaviour).  Override with
        // `--eff-tau N` to gate Sum reordering on `log10(max/min) >= N`.
        eff_tau: 0.0,
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
            // Wall-clock timeout.  `--timeout 0` disables.
            "--timeout"  | "-t" => {
                let v = iter.next().ok_or_else(||
                    "--timeout requires a value in seconds (e.g. --timeout 600 or --timeout 0 to disable)".to_string())?;
                a.timeout_secs = v.parse::<u64>().map_err(|_|
                    format!("--timeout expects a non-negative integer (seconds); got {:?}", v))?;
            }
            s if s.starts_with("--timeout=") => {
                let v = &s["--timeout=".len()..];
                a.timeout_secs = v.parse::<u64>().map_err(|_|
                    format!("--timeout expects a non-negative integer (seconds); got {:?}", v))?;
            }
            // Variance-gated Sum-reordering threshold (eff backends only).
            "--eff-tau" => {
                let v = iter.next().ok_or_else(||
                    "--eff-tau requires a value (e.g. --eff-tau 1.0; use 0 for always-reorder, inf for never-reorder)".to_string())?;
                a.eff_tau = v.parse::<f64>().map_err(|_|
                    format!("--eff-tau expects a non-negative float (or `inf`); got {:?}", v))?;
                if a.eff_tau < 0.0 || a.eff_tau.is_nan() {
                    return Err(format!("--eff-tau must be non-negative and not NaN; got {}", a.eff_tau));
                }
            }
            s if s.starts_with("--eff-tau=") => {
                let v = &s["--eff-tau=".len()..];
                a.eff_tau = v.parse::<f64>().map_err(|_|
                    format!("--eff-tau expects a non-negative float (or `inf`); got {:?}", v))?;
                if a.eff_tau < 0.0 || a.eff_tau.is_nan() {
                    return Err(format!("--eff-tau must be non-negative and not NaN; got {}", a.eff_tau));
                }
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
            "--preprocess"      => { a.preprocess = true;  }
            "--no-preprocess"   => { a.preprocess = false; }
            "--xor-gauss"       => { a.xor_gauss = true;  }
            "--no-xor-gauss"    => { a.xor_gauss = false; }
            "--symbreak"        => { a.symbreak = Some(true);  }
            "--no-symbreak"     => { a.symbreak = Some(false); }
            "--cook"            => { a.cook = true;  }
            "--no-cook"         => { a.cook = false; }
            "--satsuma-verify-secs" => {
                let v = iter.next().ok_or_else(||
                    "--satsuma-verify-secs requires a value (seconds; 0 = unlimited)".to_string())?;
                a.satsuma_verify_secs = v.parse::<u64>().map_err(|_|
                    format!("--satsuma-verify-secs expects a non-negative integer; got {:?}", v))?;
            }
            s2 if s2.starts_with("--satsuma-verify-secs=") => {
                let v = &s2["--satsuma-verify-secs=".len()..];
                a.satsuma_verify_secs = v.parse::<u64>().map_err(|_|
                    format!("--satsuma-verify-secs expects a non-negative integer; got {:?}", v))?;
            }
            "--satsuma-mem-gb" => {
                let v = iter.next().ok_or_else(||
                    "--satsuma-mem-gb requires a value (GiB; 0 = uncapped)".to_string())?;
                a.satsuma_mem_gb = v.parse::<u64>().map_err(|_|
                    format!("--satsuma-mem-gb expects a non-negative integer; got {:?}", v))?;
            }
            s2 if s2.starts_with("--satsuma-mem-gb=") => {
                let v = &s2["--satsuma-mem-gb=".len()..];
                a.satsuma_mem_gb = v.parse::<u64>().map_err(|_|
                    format!("--satsuma-mem-gb expects a non-negative integer; got {:?}", v))?;
            }
            // Cap on input clauses for which preprocess runs (0 = no cap).
            "--preprocess-max-clauses" => {
                let v = iter.next().ok_or_else(||
                    "--preprocess-max-clauses requires a value (clause count; 0 = no cap)".to_string())?;
                a.preprocess_max_clauses = v.parse::<usize>().map_err(|_|
                    format!("--preprocess-max-clauses expects a non-negative integer; got {:?}", v))?;
            }
            s if s.starts_with("--preprocess-max-clauses=") => {
                let v = &s["--preprocess-max-clauses=".len()..];
                a.preprocess_max_clauses = v.parse::<usize>().map_err(|_|
                    format!("--preprocess-max-clauses expects a non-negative integer; got {:?}", v))?;
            }
            // Cap on input clauses for which the XOR-GE pass runs (0 = no cap).
            "--xor-gauss-max-clauses" => {
                let v = iter.next().ok_or_else(||
                    "--xor-gauss-max-clauses requires a value (clause count; 0 = no cap)".to_string())?;
                a.xor_gauss_max_clauses = v.parse::<usize>().map_err(|_|
                    format!("--xor-gauss-max-clauses expects a non-negative integer; got {:?}", v))?;
            }
            s if s.starts_with("--xor-gauss-max-clauses=") => {
                let v = &s["--xor-gauss-max-clauses=".len()..];
                a.xor_gauss_max_clauses = v.parse::<usize>().map_err(|_|
                    format!("--xor-gauss-max-clauses expects a non-negative integer; got {:?}", v))?;
            }
            "--emit-cover" => {
                let v = iter.next().ok_or_else(||
                    "--emit-cover requires a file path (e.g. --emit-cover proof.cover)".to_string())?;
                a.emit_cover = Some(v.into());
            }
            s if s.starts_with("--emit-cover=") => {
                a.emit_cover = Some(s["--emit-cover=".len()..].to_string().into());
            }
            "--emit-drat" => {
                let v = iter.next().ok_or_else(||
                    "--emit-drat requires a file path (e.g. --emit-drat proof.drat)".to_string())?;
                a.emit_drat = Some(v.into());
            }
            s if s.starts_with("--emit-drat=") => {
                a.emit_drat = Some(s["--emit-drat=".len()..].to_string().into());
            }
            "--emit-pbp" => {
                let v = iter.next().ok_or_else(||
                    "--emit-pbp requires a file path (e.g. --emit-pbp proof.pbp)".to_string())?;
                a.emit_pbp = Some(v.into());
            }
            s if s.starts_with("--emit-pbp=") => {
                a.emit_pbp = Some(s["--emit-pbp=".len()..].to_string().into());
            }
            "--emit-cook-pbp" => {
                let v = iter.next().ok_or_else(||
                    "--emit-cook-pbp requires a file path".to_string())?;
                a.emit_cook_pbp = Some(v.into());
            }
            s if s.starts_with("--emit-cook-pbp=") => {
                a.emit_cook_pbp = Some(s["--emit-cook-pbp=".len()..].to_string().into());
            }
            "--proof" => {
                let v = iter.next().ok_or_else(||
                    "--proof requires a file path".to_string())?;
                a.proof = Some(v.into());
            }
            s if s.starts_with("--proof=") => {
                a.proof = Some(s["--proof=".len()..].to_string().into());
            }
            "--engine" => {
                let v = iter.next().ok_or_else(||
                    "--engine requires cadical|kissat".to_string())?;
                a.engine = v.to_string();
            }
            s if s.starts_with("--engine=") => {
                a.engine = s["--engine=".len()..].to_string();
            }
            "--elab-time-s" => {
                let v = iter.next().ok_or_else(||
                    "--elab-time-s requires a number".to_string())?;
                a.elab_time_s = v.parse().map_err(|_| "bad --elab-time-s".to_string())?;
            }
            s if s.starts_with("--elab-time-s=") => {
                a.elab_time_s = s["--elab-time-s=".len()..].parse()
                    .map_err(|_| "bad --elab-time-s".to_string())?;
            }
            "--elab-mem-mb" => {
                let v = iter.next().ok_or_else(||
                    "--elab-mem-mb requires a number".to_string())?;
                a.elab_mem_mb = v.parse().map_err(|_| "bad --elab-mem-mb".to_string())?;
            }
            s if s.starts_with("--elab-mem-mb=") => {
                a.elab_mem_mb = s["--elab-mem-mb=".len()..].parse()
                    .map_err(|_| "bad --elab-mem-mb".to_string())?;
            }
            "--elab-jobs" => {
                let v = iter.next().ok_or_else(||
                    "--elab-jobs requires a number".to_string())?;
                a.elab_jobs = v.parse().map_err(|_| "bad --elab-jobs".to_string())?;
            }
            s if s.starts_with("--elab-jobs=") => {
                a.elab_jobs = s["--elab-jobs=".len()..].parse()
                    .map_err(|_| "bad --elab-jobs".to_string())?;
            }
            "--initial-phases" => {
                let v = iter.next().ok_or_else(||
                    "--initial-phases requires a file path".to_string())?;
                a.initial_phases = Some(v.into());
            }
            s if s.starts_with("--initial-phases=") => {
                a.initial_phases = Some(s["--initial-phases=".len()..].into());
            }
            "--help"     | "-h" => {
                eprintln!("Usage: sat [--backend NAME] [--timeout SECS] [--progress] < problem.cnf");
                eprintln!();
                eprintln!("  --backend NAME, -b NAME");
                eprintln!("                    Select the search backend.  NAME is one of:");
                eprintln!("                      smart        — matrix.smart");
                eprintln!("                                     SmartController, single-DFS");
                eprintln!("                      cdcl         — matrix.cdcl");
                eprintln!("                                     CdclController, single-DFS");
                eprintln!("                      eff          — matrix.eff (default)");
                eprintln!("                                     CdclController + Effective layer,");
                eprintln!("                                     single-DFS, no dual overhead");
                eprintln!("                      eff_cover    — eff policy on the cover-emitting NNF");
                eprintln!("                                     engine; supports --emit-cover (proof");
                eprintln!("                                     substrate for open evolution)");
                eprintln!("                      greedy_cdcl  — greedy × CdclDualPath, dual");
                eprintln!("                      greedy_eff   — greedy × Effective + CDCL, dual");
                eprintln!("                                     (strongest on structured benches)");
                eprintln!("                      basic_eff    — basic × Effective + CDCL, dual");
                eprintln!("                                     (no upfront pair-mining — much");
                eprintln!("                                     cheaper than greedy_eff on big CNFs)");
                eprintln!("                      effb         — eff with engine bubble-up on restart");
                eprintln!("                                     (EXPERIMENTAL: known wrong-UNSAT mode;");
                eprintln!("                                     verify UNSATs against cdcl/cadical)");
                eprintln!("                      greedy_effb  — greedy_eff + bubble-up (same caveat)");
                eprintln!("                      basic_effb   — basic_eff + bubble-up (same caveat)");
                eprintln!("                      cadical      — bundled CaDiCaL reference solver");
                eprintln!("                      pb-cadical   — verified portfolio: Cook PB-prover");
                eprintln!("                                     for structured shapes, else CaDiCaL");
                eprintln!("                                     (--lrat); every proof machine-checkable");
                eprintln!("  --proof FILE      Proof output for pb-cadical (UNSAT verdicts).");
                eprintln!("                    Cook path: VeriPB pbp (veripb <cnf> FILE);");
                eprintln!("                    CaDiCaL path: LRAT (cake_lpr <cnf> FILE);");
                eprintln!("                    kissat path: GRAT (gratchk unsat <cnf> FILE).");
                eprintln!("                    The format is on stderr: c pb-cadical: proof-format=…");
                eprintln!("  --engine NAME     CDCL engine for pb-cadical/hydra: cadical (default,");
                eprintln!("                    native LRAT), kissat (binary DRAT, elaborated to GRAT");
                eprintln!("                    via gratgen and checked by gratchk), or portfolio[:pct]");
                eprintln!("                    — kissat for the first pct% (default 10) of the budget,");
                eprintln!("                    then cadical.");
                eprintln!("  --elab-jobs N     gratgen worker threads for DRAT->GRAT (default 8).");
                eprintln!("  --initial-phases FILE  Neural warm-start: seed cdcl/eff phase-saving");
                eprintln!("                    from predicted per-variable phases (signed DIMACS");
                eprintln!("                    lits, 0-terminated; see neural/phase_infer.py).");
                eprintln!("                    Requires --no-preprocess.");
                eprintln!("                      hydra        — pb-cadical + an XOR/parity stage:");
                eprintln!("                                     GF(2) elimination decides pure-parity");
                eprintln!("                                     formulas and simplifies mixed ones");
                eprintln!("  --timeout SECS, -t SECS");
                eprintln!("                    Hard wall-clock limit.  On timeout, prints");
                eprintln!("                    'c TIMEOUT after Ns' and exits 124.  Default: {}.",
                          DEFAULT_TIMEOUT_SECS);
                eprintln!("                    Pass --timeout 0 to disable.");
                eprintln!("  --eff-tau TAU     Variance-gated Sum-reordering threshold for eff");
                eprintln!("                    backends (eff, effb, greedy_eff, basic_eff,");
                eprintln!("                    greedy_effb, basic_effb).  Reorder a Sum's children");
                eprintln!("                    only when log10(max_count / min_count) >= TAU.");
                eprintln!("                    Default 0 = always reorder (legacy).  Try 1.0 to");
                eprintln!("                    suppress reordering on uniform-cost formulas (Steiner,");
                eprintln!("                    PHP-like, random 3-SAT) where eff hurts CDCL.");
                eprintln!("                    `inf` disables Sum reordering entirely.");
                eprintln!("  --cadical, -c     Legacy alias for --backend cadical.");
                eprintln!("  --cdcl            Legacy alias for --backend cdcl.");
                eprintln!("  --preprocess      Run NNF-level preprocessing (UP / BVE /");
                eprintln!("                    normalisation) before search.  Default ON for");
                eprintln!("                    matrix backends; no-op for cadical (its own preproc).");
                eprintln!("  --no-preprocess   Disable preprocessing.");
                eprintln!("  --preprocess-max-clauses N");
                eprintln!("                    Skip preprocess when the input has > N clauses");
                eprintln!("                    (preprocess is ~150 µs/clause).  Default 250000;");
                eprintln!("                    pass 0 for no cap (only sensible with a large -t).");
                eprintln!("  --emit-cover FILE Write a cover certificate to FILE.  On UNSAT,");
                eprintln!("                    the file contains a sound replay-able UNSAT proof");
                eprintln!("                    (every CoveredPathPrefix event the search emits).");
                eprintln!("                    Validate with `sat-cover-verify <cnf> <FILE>`.");
                eprintln!("                    Only supported with --backend cdcl or smart.");
                eprintln!("  --emit-drat FILE  Write a DRAT proof to FILE.  On UNSAT, contains");
                eprintln!("                    every CDCL learned clause as a DIMACS line plus");
                eprintln!("                    a final `0` for the empty clause.  Replayable by");
                eprintln!("                    `sat-drat-verify <cnf> <FILE>` or drat-trim.");
                eprintln!("                    Only supported with --backend cdcl + --no-preprocess.");
                eprintln!("  --emit-pbp FILE   Write a pseudo-Boolean (VeriPB) proof to FILE.");
                eprintln!("                    Like --emit-drat but in PB format; can express");
                eprintln!("                    cardinality reasoning via cutting-planes rules.");
                eprintln!("                    Validate with `veripb --cnf <cnf> <FILE>`.");
                eprintln!("                    Only with --backend cdcl + --no-preprocess.");
                eprintln!("  --emit-cook-pbp FILE");
                eprintln!("                    Detect PHP-N-M or RoundRobin shape in the input;");
                eprintln!("                    if matched, emit a polynomial-size Cook-style");
                eprintln!("                    PB proof to FILE without running any search.");
                eprintln!("                    On no-match, exits 3 (use --emit-pbp instead).");
                eprintln!("                    Verify with `veripb --cnf <cnf> <FILE>`.");
                eprintln!("  --progress, -p    Show a live progress bar on stderr (TTY only).");
                eprintln!("                    Press Ctrl-C to interrupt.");
                eprintln!();
                eprintln!("Default backend: eff (matrix.eff).");
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
    let (nvars, mut clauses) = match parse_dimacs(stdin.lock()) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("c parse error: {}", e);
            std::process::exit(1);
        }
    };
    eprintln!("c parsed {} variables, {} clauses", nvars, clauses.len());

    // Neural warm-start (--initial-phases): load the predicted per-variable
    // phase seed once and stash it for the cdcl/eff controller builders.
    // Requires --no-preprocess so seed indices match the input CNF variables.
    if let Some(pf) = args.initial_phases.as_ref() {
        if args.preprocess {
            eprintln!("c ERROR: --initial-phases requires --no-preprocess \
                       (seed indices must match the input CNF variables)");
            std::process::exit(2);
        }
        match load_initial_phases(pf, nvars) {
            Ok(seed) => {
                let n = seed.iter().filter(|s| s.is_some()).count();
                let _ = INITIAL_PHASES.set(seed);
                eprintln!("c warm-start: seeded {}/{} variable phases from {}",
                          n, nvars, pf.display());
            }
            Err(e) => { eprintln!("c ERROR: {}", e); std::process::exit(2); }
        }
    }

    // --emit-cook-pbp short-circuit.  When set, attempt to detect
    // PHP-N-M or RoundRobin shape in the input.  On match, emit a
    // polynomial-size VeriPB proof and exit UNSAT — no search needed.
    // On no-match, exit with an error so callers know to use
    // `--emit-pbp` or accept the matrix-method's regular path.
    if let Some(out) = args.emit_cook_pbp.as_ref() {
        use logic::cook_pbp::{detect_shape, emit_proof, CnfShape};
        let t_detect = Instant::now();
        let shape = detect_shape(&clauses, nvars);
        let detect_ms = t_detect.elapsed().as_secs_f64() * 1000.0;
        match shape {
            CnfShape::Unknown => {
                eprintln!("c emit-cook-pbp: no matching shape detected \
                           in {:.1}ms (try --emit-pbp instead)", detect_ms);
                std::process::exit(3);
            }
            ref s => {
                eprintln!("c emit-cook-pbp: detected {} in {:.1}ms",
                          s.describe(), detect_ms);
                let t_emit = Instant::now();
                let f = match std::fs::File::create(out) {
                    Ok(f) => f,
                    Err(e) => {
                        eprintln!("c ERROR: cannot create cook-pbp file {}: {}",
                                  out.display(), e);
                        std::process::exit(2);
                    }
                };
                let mut w = io::BufWriter::new(f);
                if let Err(e) = emit_proof(s, clauses.len(), &mut w) {
                    eprintln!("c ERROR: cook-pbp emission failed: {}", e);
                    std::process::exit(1);
                }
                let emit_ms = t_emit.elapsed().as_secs_f64() * 1000.0;
                eprintln!("c emit-cook-pbp: wrote {} in {:.1}ms",
                          out.display(), emit_ms);
                eprintln!("c UNSAT in {:.1}ms (by Cook-PBP construction)",
                          detect_ms + emit_ms);
                println!("s UNSATISFIABLE");
                return;
            }
        }
    }

    // pb-cadical backend: verified portfolio.  Try the standalone Cook
    // PB-prover first (structure -> polynomial VeriPB proof); on no match,
    // shell out to the CaDiCaL binary with --veripb so its proof is also
    // VeriPB-checkable.  Either way a solved instance carries a verifiable
    // certificate.  Short-circuits before the matrix search.
    if matches!(args.backend, BackendChoice::PbCadical | BackendChoice::Hydra | BackendChoice::HydraSymBreak | BackendChoice::HydraSatsuma | BackendChoice::Satsuma) {
        use logic::cook_pbp::{detect_shape, emit_proof, CnfShape};
        use std::io::Write as _;
        let bk = args.backend.name();
        let t0 = Instant::now();
        // Cook shapes are all small instances (largest detection in either
        // competition set: <1M clauses); skip the detectors on giants so
        // structure analysis never eats meaningful engine budget there.
        let try_cook = args.cook
            && !matches!(args.backend, BackendChoice::Satsuma)
            && clauses.len() <= 1_000_000;
        // Backstop watchdog: the main watchdog spawns after this block, and
        // hydra's XOR stage can run minutes on 100k+-var parity systems.
        // CaDiCaL gets its own (budget-split) -t below, so fire with a 60s
        // grace period so the graceful CaDiCaL-timeout path wins the race
        // whenever CaDiCaL is the active stage.
        // Once a verdict + timing line is printed, the backstop must NOT
        // print "c TIMEOUT after" — that would overwrite the recorded
        // verdict in run_benchmark's parser (last line wins) and destroy a
        // genuine solve whose proof post-processing ran long.
        let verdict_done = std::sync::Arc::new(std::sync::atomic::AtomicBool::new(false));
        if args.timeout_secs > 0 {
            // Grace covers post-verdict work: drat-trim elaboration gets its
            // own bounded budget (--elab-time-s, default = --timeout), so the
            // backstop is sized to outlive it.
            let elab_budget = if args.engine != "cadical" && args.proof.is_some() {
                if args.elab_time_s > 0 { args.elab_time_s } else { args.timeout_secs }
            } else {
                0
            };
            let limit = args.timeout_secs + elab_budget + 60;
            let vd = verdict_done.clone();
            std::thread::spawn(move || {
                std::thread::sleep(std::time::Duration::from_secs(limit));
                if !vd.load(std::sync::atomic::Ordering::Relaxed) {
                    eprintln!("c TIMEOUT after {:.1}ms", (limit as f64) * 1000.0);
                }
                std::process::exit(124);
            });
        }
        let shape = if try_cook {
            detect_shape(&clauses, nvars)
        } else {
            CnfShape::Unknown
        };
        if !matches!(shape, CnfShape::Unknown) {
            eprintln!("c {}: prover=cook", bk);
            eprintln!("c {}: proof-format=pbp", bk);
            eprintln!("c {}: Cook shape {} in {:.1}ms -> PB proof",
                      bk, shape.describe(), t0.elapsed().as_secs_f64() * 1000.0);
            if let Some(out) = args.proof.as_ref() {
                match std::fs::File::create(out) {
                    Ok(f) => {
                        let mut w = io::BufWriter::new(f);
                        if let Err(e) = emit_proof(&shape, clauses.len(), &mut w) {
                            eprintln!("c ERROR: cook-pbp emission failed: {}", e);
                            std::process::exit(1);
                        }
                        eprintln!("c {}: wrote VeriPB proof {}", bk, out.display());
                    }
                    Err(e) => {
                        eprintln!("c ERROR: cannot create proof {}: {}", out.display(), e);
                        std::process::exit(2);
                    }
                }
            }
            // Standard timing line so run_benchmark's parser records the time.
            eprintln!("c UNSAT in {:.1}ms", t0.elapsed().as_secs_f64() * 1000.0);
            println!("s UNSATISFIABLE");
            return;
        }
        // No structural shape.  Hydra inserts the XOR/parity stage here;
        // pb-cadical goes straight to CaDiCaL.
        let mut xor_simplified: Option<(Vec<Vec<i32>>, Vec<Option<bool>>)> = None;
        if matches!(args.backend, BackendChoice::Hydra | BackendChoice::HydraSymBreak | BackendChoice::HydraSatsuma) && clauses.len() <= 5_000_000 {
            use logic::xor_gauss::{solve_xor_system, XorGaussResult};
            let t_x = Instant::now();
            eprintln!("c {}: structure analysis (xor stage)…", bk);
            match solve_xor_system(nvars, &clauses, 50_000_000) {
                XorGaussResult::Unsat { by_bcp } => {
                    eprintln!("c {}: prover=xor", bk);
                    if by_bcp {
                        eprintln!("c {}: unit propagation refutes the formula \
                                   ({:.1}ms) -> UNSAT",
                                  bk, t_x.elapsed().as_secs_f64() * 1000.0);
                    } else {
                        eprintln!("c {}: XOR system inconsistent (GF(2) GE, {:.1}ms) -> UNSAT",
                                  bk, t_x.elapsed().as_secs_f64() * 1000.0);
                    }
                    // Certify with a GN21 parity PB proof.  The certifier does
                    // its own STRICT recovery (complete canonical encodings
                    // only), so it can decline even though the (laxer) solving
                    // recovery refuted — then the verdict stands uncertified.
                    let mut certified = false;
                    if by_bcp {
                        // A BCP refutation has the simplest certificate of
                        // all: VeriPB unit-propagates the formula to the
                        // conflict, so the whole proof is one `rup >= 1`.
                        if let Some(out) = args.proof.as_ref() {
                            if let Ok(f) = std::fs::File::create(out) {
                                let mut w = io::BufWriter::new(f);
                                let ok = writeln!(w, "pseudo-Boolean proof version 3.0")
                                    .and_then(|_| writeln!(w, "f {};", clauses.len()))
                                    .and_then(|_| writeln!(w, "rup >= 1 ;"))
                                    .and_then(|_| writeln!(w, "output NONE;"))
                                    .and_then(|_| writeln!(w, "conclusion UNSAT : -1;"))
                                    .and_then(|_| writeln!(w, "end pseudo-Boolean proof;"));
                                if ok.is_ok() {
                                    certified = true;
                                    eprintln!("c {}: proof-format=pbp", bk);
                                    eprintln!("c {}: wrote trivial RUP proof {}", bk,
                                              out.display());
                                }
                            }
                        }
                    }
                    if let (false, Some(out)) = (certified, args.proof.as_ref()) {
                        use logic::parity_pbp::{detect_parity_refutation, emit_parity_proof};
                        let t_p = Instant::now();
                        if let Some(pr) = detect_parity_refutation(&clauses) {
                            match std::fs::File::create(out) {
                                Ok(f) => {
                                    let mut w = io::BufWriter::new(f);
                                    if emit_parity_proof(&pr, clauses.len(), nvars, &mut w).is_ok() {
                                        certified = true;
                                        eprintln!("c {}: proof-format=pbp", bk);
                                        eprintln!("c {}: wrote GN21 parity proof {} ({} XORs in \
                                                   refutation, {:.1}ms)",
                                                  bk, out.display(), pr.subset.len(),
                                                  t_p.elapsed().as_secs_f64() * 1000.0);
                                    }
                                }
                                Err(e) => {
                                    eprintln!("c ERROR: cannot create proof {}: {}", out.display(), e);
                                }
                            }
                        }
                    }
                    if !certified {
                        eprintln!("c {}: proof-format=none", bk);
                        if let Some(out) = args.proof.as_ref() { let _ = std::fs::remove_file(out); }
                    }
                    eprintln!("c UNSAT in {:.1}ms", t0.elapsed().as_secs_f64() * 1000.0);
                    println!("s UNSATISFIABLE");
                    return;
                }
                XorGaussResult::Sat(model) => {
                    eprintln!("c {}: prover=xor", bk);
                    eprintln!("c {}: proof-format=witness", bk);
                    eprintln!("c {}: pure-XOR satisfiable (GF(2) GE, {:.1}ms); the model is \
                               the certificate", bk, t_x.elapsed().as_secs_f64() * 1000.0);
                    if let Some(out) = args.proof.as_ref() { let _ = std::fs::remove_file(out); }
                    eprintln!("c SAT in {:.1}ms", t0.elapsed().as_secs_f64() * 1000.0);
                    println!("s SATISFIABLE");
                    let mut line = String::from("v");
                    for (i, &b) in model.iter().enumerate() {
                        line.push(' ');
                        if !b { line.push('-'); }
                        line.push_str(&(i + 1).to_string());
                        if line.len() > 70 {
                            println!("{}", line);
                            line = String::from("v");
                        }
                    }
                    println!("{} 0", line);
                    return;
                }
                XorGaussResult::Simplified { clauses: simp, forced, recovered, forced_count } => {
                    if args.proof.is_none() {
                        eprintln!("c {}: xor stage: {} XOR(s), {} var(s) GE-forced; residual \
                                   {} clauses ({:.1}ms)", bk, recovered, forced_count,
                                  simp.len(), t_x.elapsed().as_secs_f64() * 1000.0);
                        xor_simplified = Some((simp, forced));
                    } else {
                        // Certified mode: solving the GE-simplified residual
                        // would make the engine's proof useless against the
                        // ORIGINAL formula (the s38417 class).  Solve the
                        // original instead — full LRAT certification beats
                        // the simplification.  (Certifying the forced units
                        // via a DRAT prefix is future work.)
                        eprintln!("c {}: xor stage: {} XOR(s), {} var(s) GE-forced — \
                                   ignored in certified mode ({:.1}ms)",
                                  bk, recovered, forced_count,
                                  t_x.elapsed().as_secs_f64() * 1000.0);
                    }
                }
                XorGaussResult::Indeterminate { recovered, .. } => {
                    if recovered > 0 {
                        eprintln!("c {}: xor stage: {} XOR(s) recovered, no usable consequence \
                                   ({:.1}ms)", bk, recovered, t_x.elapsed().as_secs_f64() * 1000.0);
                    }
                }
            }
        }
        let solve_clauses: &[Vec<i32>] =
            xor_simplified.as_ref().map(|(s, _)| s.as_slice()).unwrap_or(&clauses);
        let forced: Option<&Vec<Option<bool>>> = xor_simplified.as_ref().map(|(_, f)| f);

        // Symmetry-breaking stage (hydra only, `logic::symbreak`): detect
        // the formula's automorphisms and add lex-leader SBP clauses before
        // the CaDiCaL handoff. Gated to a size where the (not-yet-dejavu-fast)
        // IR search is affordable, and skipped on a GE-simplified residual so
        // the two transforms don't stack. SBPs are satisfiability-preserving:
        // a SAT model of the augmented formula, projected to the original
        // variables, is a genuine model (the model print below caps at
        // `nvars`); UNSAT stays sound (equisatisfiable) but uncertified until
        // the SR/VeriPB symmetry proof (Phase 6), so `emit_lrat` is forced off.
        const SB_VAR_CAP: usize = 50_000;
        const SB_CLAUSE_CAP: usize = 200_000;
        let mut aug_clauses: Vec<Vec<i32>> = Vec::new();
        let mut aug_nvars = nvars;
        let mut symbroke = false;
        let want_symbreak = args
            .symbreak
            .unwrap_or(matches!(args.backend, BackendChoice::HydraSymBreak));
        if matches!(args.backend, BackendChoice::Hydra | BackendChoice::HydraSymBreak)
            && want_symbreak
            && forced.is_none()
            && nvars <= SB_VAR_CAP
            && solve_clauses.len() <= SB_CLAUSE_CAP
        {
            let t_sb = Instant::now();
            // Detection budget: never let the (not-yet-dejavu-fast) IR search
            // dominate — cap at min(3s, 10% of the remaining wall-clock). On a
            // labeling the naive search handles poorly it aborts and uses the
            // sound partial generator set (or none, falling through to plain
            // CaDiCaL), so the stage is a strict Pareto safety.
            let sb_budget = if args.timeout_secs > 0 {
                let remain = args.timeout_secs.saturating_sub(t0.elapsed().as_secs()).max(1);
                std::time::Duration::from_secs_f64((remain as f64 * 0.10).min(3.0).max(0.2))
            } else {
                std::time::Duration::from_secs(3)
            };
            // Run detection on a worker thread and hard-abandon it past the
            // budget: the internal deadline stops the (dominant) IR search,
            // but Schreier-Sims reduction is not deadline-perfect, so a
            // recv_timeout is the bulletproof guarantee the stage never
            // blocks the solve. An abandoned thread self-terminates via its
            // deadline; a SAT-preserving stage that produces nothing is fine.
            let (added, newn) = {
                let owned: Vec<Vec<i32>> = solve_clauses.to_vec();
                let dl = t_sb + sb_budget;
                let (tx, rx) = std::sync::mpsc::channel();
                std::thread::spawn(move || {
                    let r = logic::symbreak::break_symmetries_within(nvars, &owned, Some(dl));
                    let _ = tx.send(r);
                });
                match rx.recv_timeout(sb_budget + std::time::Duration::from_millis(500)) {
                    Ok(r) => r,
                    Err(_) => {
                        eprintln!("c {}: symmetry stage: detection over budget, skipped", bk);
                        (Vec::new(), nvars)
                    }
                }
            };
            if added.is_empty() {
                eprintln!("c {}: symmetry stage: no symmetry found ({:.1}ms)",
                          bk, t_sb.elapsed().as_secs_f64() * 1000.0);
            } else {
                eprintln!("c {}: symmetry stage: {} SBP clauses, +{} aux vars ({:.1}ms) \
                           -> augmented solve", bk, added.len(), newn - nvars,
                          t_sb.elapsed().as_secs_f64() * 1000.0);
                aug_clauses.reserve(solve_clauses.len() + added.len());
                aug_clauses.extend_from_slice(solve_clauses);
                aug_clauses.extend(added);
                aug_nvars = newn;
                symbroke = true;
            }
        }
        // The CNF actually handed to the engine (augmented when symbroke).
        let (solve_clauses, solve_nvars): (&[Vec<i32>], usize) = if symbroke {
            (&aug_clauses, aug_nvars)
        } else {
            (solve_clauses, nvars)
        };

        // hydra_satsuma / satsuma fall-through: hand the formula to the SAT
        // Comp 2026 winner satsuma-iter+kissat inside its Docker image, in
        // TWO bounded container runs so nothing here is ever unwatched:
        //   A) solve  — satsuma (binary-SR symmetry proof) + kissat (appends
        //      its refutation), under `timeout` at the remaining budget minus
        //      a 2s margin so it returns before the backstop watchdog fires;
        //   B) verify — on a non-GE UNSAT, dsr-trim checks the COMPOSED proof
        //      against the exact CNF handed over, under its own budget
        //      (--satsuma-verify-secs, default 600, 0 = unlimited), AFTER the
        //      verdict + timing line are printed and verdict_done is set (the
        //      watchdog stands down, and solve-time accounting excludes
        //      verification, matching how the LRAT paths are timed).
        // --satsuma-mem-gb caps each container (docker --memory); 0 =
        // uncapped, competition-faithful — the Docker VM allocation still
        // binds overall. A dsr-trim timeout/failure downgrades the UNSAT to
        // sound-but-UNCERTIFIED; the verdict itself is never lost.
        if matches!(args.backend, BackendChoice::HydraSatsuma | BackendChoice::Satsuma) {
            // Mount dir under /tmp: Docker Desktop's default file sharing
            // covers /private/tmp, while std::env::temp_dir()'s
            // /var/folders/... may not be shared.
            let mdir = std::path::PathBuf::from(format!("/tmp/pbsatsuma-{}", std::process::id()));
            if let Err(e) = std::fs::create_dir_all(&mdir) {
                eprintln!("c ERROR: satsuma mount dir: {}", e);
                std::process::exit(2);
            }
            let cnf_path = mdir.join("f.cnf");
            {
                let f = match std::fs::File::create(&cnf_path) {
                    Ok(f) => f,
                    Err(e) => { eprintln!("c ERROR: satsuma cnf: {}", e); std::process::exit(2); }
                };
                let mut w = io::BufWriter::new(f);
                let _ = writeln!(w, "p cnf {} {}", solve_nvars, solve_clauses.len());
                for c in solve_clauses {
                    for &l in c { let _ = write!(w, "{} ", l); }
                    let _ = writeln!(w, "0");
                }
            }
            let mem_flags: Vec<String> = if args.satsuma_mem_gb > 0 {
                vec![format!("--memory={}g", args.satsuma_mem_gb),
                     format!("--memory-swap={}g", args.satsuma_mem_gb)]
            } else {
                Vec::new()
            };
            let docker_run = |inner: &str| -> std::io::Result<std::process::Output> {
                let mut cmd = std::process::Command::new("docker");
                cmd.args(["run", "--rm"]);
                for m in &mem_flags { cmd.arg(m); }
                cmd.arg("-v")
                    .arg(format!("{}:/work", mdir.display()))
                    .args(["satsuma-iter-kissat", "bash", "-c"])
                    .arg(inner);
                cmd.output()
            };
            // Phase A: solve. 2s under the remaining budget so the container
            // self-terminates (and docker returns) before the backstop
            // watchdog would exit(124) and orphan the wait.
            let remaining = if args.timeout_secs > 0 {
                args.timeout_secs.saturating_sub(t0.elapsed().as_secs()).max(1)
            } else {
                0
            };
            let solve_budget = if remaining > 0 { remaining.saturating_sub(2).max(1) } else { 0 };
            // Size guard the winning submission shipped commented-out (their
            // nodes had 128 GB; a Docker Desktop VM does not): satsuma's
            // literal graph on multi-million-var instances (md5-equivalence:
            // 9.4M vars / 25M clauses) is several GB per worker and gets
            // OOM-killed in seconds under -j 10. Above the caps, skip satsuma
            // and run kissat directly on the raw formula — still solved, and
            // an UNSAT proof is still dsr-trim-checkable (kissat's clausal
            // steps are the suffix of every composed proof).
            const SATSUMA_VAR_CAP: usize = 1_000_000;
            const SATSUMA_CLAUSE_CAP: usize = 25_000_000;
            let satsuma_fits = solve_nvars < SATSUMA_VAR_CAP
                && solve_clauses.len() < SATSUMA_CLAUSE_CAP;
            if !satsuma_fits {
                eprintln!("c {}: size guard ({} vars / {} clauses): satsuma skipped -> kissat direct",
                          bk, solve_nvars, solve_clauses.len());
            }
            let inner_solve = if satsuma_fits {
                format!("cd /src && {}./run_satsuma_kissat.sh /work/f.cnf /work",
                        if solve_budget > 0 { format!("timeout {}s ", solve_budget) } else { String::new() })
            } else {
                format!("cd /src && {}./kissat /work/f.cnf /work/proof.out",
                        if solve_budget > 0 { format!("timeout {}s ", solve_budget) } else { String::new() })
            };
            eprintln!("c {}: {} -> satsuma-iter+kissat (docker){}{}", bk,
                      if forced.is_some() { "GE-simplified residual" }
                      else if matches!(args.backend, BackendChoice::Satsuma) { "raw formula" }
                      else { "no Cook shape" },
                      if solve_budget > 0 { format!(" budget={}s", solve_budget) } else { String::new() },
                      if args.satsuma_mem_gb > 0 { format!(" mem={}g", args.satsuma_mem_gb) } else { String::new() });
            let out = match docker_run(&inner_solve) {
                Ok(o) => o,
                Err(e) => {
                    eprintln!("c ERROR: docker run failed: {} (build the image with tools/satsuma/build.sh)", e);
                    let _ = std::fs::remove_dir_all(&mdir);
                    std::process::exit(2);
                }
            };
            let stdout = String::from_utf8_lossy(&out.stdout);
            let mut verdict: Option<&str> = None;
            let mut vline: Vec<i32> = Vec::new();
            for line in stdout.lines() {
                if let Some(rest) = line.strip_prefix("s ") {
                    let v = rest.trim();
                    if v == "SATISFIABLE" || v == "UNSATISFIABLE" { verdict = Some(if v == "SATISFIABLE" { "SAT" } else { "UNSAT" }); }
                } else if let Some(rest) = line.strip_prefix("v ") {
                    for tok in rest.split_whitespace() {
                        if let Ok(l) = tok.parse::<i32>() {
                            if l != 0 { vline.push(l); }
                        }
                    }
                }
            }
            let el_ms = t0.elapsed().as_secs_f64() * 1000.0;
            if verdict.is_some() {
                eprintln!("c {}: prover=satsuma-kissat", bk);
            }
            match verdict {
                Some("UNSAT") => {
                    // Verdict + timing land FIRST; the watchdog stands down;
                    // verification never eats into either.
                    eprintln!("c UNSAT in {:.1}ms", el_ms);
                    verdict_done.store(true, std::sync::atomic::Ordering::Relaxed);
                    if forced.is_some() {
                        eprintln!("c {}: UNSAT of GE residual (sound; SR certificate covers \
                                   the residual only — uncertified for the original)", bk);
                    } else {
                        // Phase B: bounded in-container dsr-trim verification.
                        let vb = args.satsuma_verify_secs;
                        eprintln!("c {}: verifying composed SR proof (dsr-trim{})…", bk,
                                  if vb > 0 { format!(", budget {}s", vb) } else { ", unbounded".into() });
                        let inner_verify = format!(
                            "cd /src && r=$({}./dsr-trim/bin/dsr-trim -f /work/f.cnf /work/proof.out /dev/null 2>/dev/null | grep '^s '; exit ${{PIPESTATUS[0]}}); rc=$?; \
                             if [ -n \"$r\" ]; then echo \"c dsrtrim: $r\"; \
                             elif [ $rc = 124 ]; then echo 'c dsrtrim: TIMEOUT'; \
                             else echo \"c dsrtrim: FAILED rc=$rc\"; fi",
                            if vb > 0 { format!("timeout {}s ", vb) } else { String::new() });
                        let vout = docker_run(&inner_verify);
                        let vtext = vout.as_ref().map(|o| String::from_utf8_lossy(&o.stdout).to_string())
                            .unwrap_or_default();
                        if vtext.contains("c dsrtrim: s VERIFIED UNSAT") {
                            eprintln!("c {}: dsr-trim VERIFIED UNSAT (composed satsuma SR + kissat \
                                       refutation checks against the input formula)", bk);
                            if let Some(p) = args.proof.as_ref() {
                                match std::fs::copy(mdir.join("proof.out"), p) {
                                    Ok(_) => eprintln!("c {}: SR proof copied to {} (binary SR — check \
                                                        with dsr-trim, not cake_lpr)", bk, p.display()),
                                    Err(e) => eprintln!("c {}: SR proof copy failed: {}", bk, e),
                                }
                            }
                        } else if vtext.contains("c dsrtrim: TIMEOUT") {
                            eprintln!("c {}: dsr-trim verification TIMEOUT (>{}s) — UNSAT is \
                                       sound-if-kissat-correct but UNCERTIFIED", bk, vb);
                        } else {
                            eprintln!("c {}: WARNING dsr-trim did NOT verify the proof — verdict \
                                       sound-if-kissat-correct but UNCERTIFIED", bk);
                        }
                    }
                    println!("s UNSATISFIABLE");
                }
                Some("SAT") => {
                    eprintln!("c SAT in {:.1}ms", el_ms);
                    verdict_done.store(true, std::sync::atomic::Ordering::Relaxed);
                    eprintln!("c {}: model over satsuma-augmented vars projected to the \
                               original {} (model is the certificate)", bk, nvars);
                    println!("s SATISFIABLE");
                    // Project: satsuma's SBP aux vars sit above the original
                    // range; original clauses mention only 1..=nvars, and on a
                    // GE residual the forced units overwrite eliminated vars.
                    let mut sign = vec![true; nvars + 1];
                    for &l in &vline {
                        let v = l.unsigned_abs() as usize;
                        if v <= nvars { sign[v] = l > 0; }
                    }
                    if let Some(f) = forced {
                        for (i, ov) in f.iter().enumerate() {
                            if let Some(b) = ov {
                                if i + 1 <= nvars { sign[i + 1] = *b; }
                            }
                        }
                    }
                    let mut line = String::from("v");
                    for v in 1..=nvars {
                        line.push(' ');
                        if !sign[v] { line.push('-'); }
                        line.push_str(&v.to_string());
                        if line.len() > 70 {
                            println!("{}", line);
                            line = String::from("v");
                        }
                    }
                    println!("{} 0", line);
                }
                _ => {
                    eprintln!("c TIMEOUT after {:.1}ms", el_ms);
                    verdict_done.store(true, std::sync::atomic::Ordering::Relaxed);
                    eprintln!("c {}: satsuma-iter+kissat reached no verdict (timeout/unknown; \
                               includes an in-container OOM kill under --satsuma-mem-gb)", bk);
                    // Surface WHY: container stdout tail + docker CLI stderr head,
                    // so a satsuma crash / OOM kill / CLI failure is diagnosable
                    // from the benchmark log instead of reading as a bare timeout.
                    for l in stdout.lines().rev().take(3).collect::<Vec<_>>().into_iter().rev() {
                        eprintln!("c {}: container-out: {}", bk, &l[..l.len().min(200)]);
                    }
                    let derr = String::from_utf8_lossy(&out.stderr);
                    for l in derr.lines().take(3) {
                        eprintln!("c {}: docker-err: {}", bk, &l[..l.len().min(200)]);
                    }
                }
            }
            let _ = std::fs::remove_dir_all(&mdir);
            return;
        }

        // Proof routing: a CaDiCaL LRAT proof is only valid against the CNF
        // CaDiCaL actually saw.  On a GE-simplified residual OR a
        // symmetry-augmented formula it would NOT certify the original, so no
        // proof is emitted there (the verdict stays sound: GE-forced units are
        // logical consequences; SBPs are satisfiability-preserving).
        let emit_lrat = args.proof.is_some() && forced.is_none() && !symbroke;
        // SAT models and v-line handling: reconstruct (cap to original vars)
        // whenever the engine saw a transformed formula.
        let reconstruct_model = forced.is_some() || symbroke;
        // Engine schedule.  "portfolio[:pct]" = kissat for the first pct% of
        // the remaining budget, then cadical for the rest.  Sizing (from the
        // 5000s baseline runs): both measured kissat wins landed at 165s/345s,
        // inside a 10% slice of T=5000, while cadical solves needing more
        // than the post-slice budget (>4500s) number only 3 (2025) + 1
        // (2026) — so pct=10 banks kissat's fast SAT wins at minimal tail
        // risk.  Single-engine modes are a 1-phase schedule.
        let portfolio_pct: Option<u64> = if args.engine == "portfolio" {
            Some(10)
        } else if let Some(p) = args.engine.strip_prefix("portfolio:") {
            Some(p.parse::<u64>().unwrap_or(10).clamp(1, 99))
        } else {
            None
        };
        let schedule: Vec<bool> = match portfolio_pct {
            Some(_) => vec![true, false],            // kissat slice, cadical rest
            None => vec![args.engine == "kissat"],
        };
        eprintln!("c {}: proof-format={}", bk, if emit_lrat { "lrat" } else { "none" });
        eprintln!("c {}: {} -> {}{} ({:.1}ms)", bk,
                  if forced.is_some() { "GE-simplified residual" } else { "no Cook shape" },
                  args.engine,
                  if emit_lrat { " (proof)" } else { "" },
                  t0.elapsed().as_secs_f64() * 1000.0);
        let tmp = std::env::temp_dir().join(format!("pbcadical-{}.cnf", std::process::id()));
        {
            let f = match std::fs::File::create(&tmp) {
                Ok(f) => f,
                Err(e) => { eprintln!("c ERROR: temp cnf: {}", e); std::process::exit(2); }
            };
            let mut w = io::BufWriter::new(f);
            let _ = writeln!(w, "p cnf {} {}", solve_nvars, solve_clauses.len());
            for c in solve_clauses {
                for &l in c { let _ = write!(w, "{} ", l); }
                let _ = writeln!(w, "0");
            }
        }
        // Kissat emits binary DRAT (no native LRAT); it goes to a temp file
        // and is elaborated to the requested proof path with `drat-trim -L`
        // after an UNSAT verdict.
        let drat_tmp = std::env::temp_dir()
            .join(format!("pbcadical-{}.drat", std::process::id()));
        // A CaDiCaL report data row is "c <marker>  <seconds> <ints…>": after
        // "c " a single non-space phase marker, then whitespace, then a digit.
        // The 2-/3-line column headers ("c  seconds …") and banner don't match.
        let is_report = |line: &str| -> bool {
            line.strip_prefix("c ").map_or(false, |r| {
                let mut ch = r.chars();
                matches!(ch.next(), Some(m) if !m.is_whitespace())
                    && ch.as_str().trim_start().starts_with(|c: char| c.is_ascii_digit())
            })
        };
        let mut verdict: Option<String> = None;
        let mut last_report: Option<String> = None;
        let mut vline: Vec<i32> = Vec::new();
        // Kissat prints clean end-of-run stat lines ("c conflicts: N …",
        // "c restarts: N …") after the s-line — including on timeout.
        let mut ks_conflicts: Option<u64> = None;
        let mut ks_restarts: Option<u64> = None;
        let mut deciding_kissat = schedule[0];
        for (pi, &ph_kissat) in schedule.iter().enumerate() {
            deciding_kissat = ph_kissat;
            let engine_name = if ph_kissat { "kissat" } else { "cadical" };
            let engine_bin = if ph_kissat {
                ["/opt/homebrew/bin/kissat", "/usr/local/bin/kissat", "/usr/bin/kissat"]
                    .iter().find(|p| std::path::Path::new(p).exists())
                    .copied().unwrap_or("kissat")
            } else {
                ["/opt/homebrew/bin/cadical", "/usr/local/bin/cadical", "/usr/bin/cadical"]
                    .iter().find(|p| std::path::Path::new(p).exists())
                    .copied().unwrap_or("cadical")
            };
            // Per-phase budget: the first portfolio phase gets its slice of
            // what the earlier stages left; the last phase gets the rest.
            // budget == 0 means "no limit" (only without a global timeout).
            let remaining = if args.timeout_secs > 0 {
                args.timeout_secs.saturating_sub(t0.elapsed().as_secs()).max(1)
            } else {
                0
            };
            let budget = match portfolio_pct {
                Some(pct) if pi + 1 < schedule.len() => {
                    if remaining > 0 {
                        // Floor of 30s (a shorter kissat phase is pointless),
                        // but never more than half the remaining budget.
                        let floor = 30.min(remaining / 2).max(1);
                        (remaining * pct / 100).max(floor).min(remaining)
                    } else {
                        600
                    }
                }
                _ => remaining,
            };
            if schedule.len() > 1 {
                eprintln!("c {}: phase {}/{}: {} budget={}",
                          bk, pi + 1, schedule.len(), engine_name,
                          if budget > 0 { format!("{}s", budget) } else { "unbounded".into() });
            }
            let mut cmd = std::process::Command::new(engine_bin);
            // Default verbosity (no -q) so the engine prints its periodic
            // report rows; stream stdout line-by-line and relay them live
            // (throttled), capturing the verdict + model en route.
            if budget > 0 {
                if ph_kissat {
                    cmd.arg(format!("--time={}", budget));
                } else {
                    cmd.arg("-t").arg(budget.to_string());
                }
            }
            // --lrat: CaDiCaL's reasoning is clausal, so emit native LRAT
            // (binary, with hints) for the fast formally-verified cake_lpr;
            // kissat writes binary DRAT to drat_tmp, elaborated below.
            if emit_lrat && !ph_kissat { cmd.arg("--lrat"); }
            cmd.arg(&tmp);
            if emit_lrat {
                if ph_kissat {
                    cmd.arg(&drat_tmp);
                } else if let Some(out) = args.proof.as_ref() {
                    cmd.arg(out);
                }
            }
            cmd.stdout(std::process::Stdio::piped());
            cmd.stderr(std::process::Stdio::null());
            let mut child = match cmd.spawn() {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("c ERROR: failed to run {} ({}): {}", engine_name, engine_bin, e);
                    continue; // a missing engine forfeits its phase only
                }
            };
            vline.clear();
            last_report = None;
            ks_conflicts = None;
            ks_restarts = None;
            if let Some(out) = child.stdout.take() {
                use std::io::BufRead as _;
                let mut last = Instant::now();
                for line in io::BufReader::new(out).lines().map_while(Result::ok) {
                    if let Some(rest) = line.strip_prefix("s ") {
                        // Engines print "s UNKNOWN" on their own timeout —
                        // that is NOT a deciding verdict (the next phase, or
                        // the TIMEOUT path, owns the outcome).
                        let v = rest.trim();
                        if v == "SATISFIABLE" || v == "UNSATISFIABLE" {
                            verdict = Some(v.to_string());
                            println!("{}", line);
                        }
                    } else if line.starts_with("v ") {
                        if reconstruct_model {
                            // Transformed (residual / symmetry-augmented) model:
                            // collect, reconstruct + print below over original vars.
                            for tok in line[2..].split_whitespace() {
                                if let Ok(l) = tok.parse::<i32>() {
                                    if l != 0 { vline.push(l); }
                                }
                            }
                        } else {
                            println!("{}", line);
                        }
                    } else if let Some(rest) = line.strip_prefix("c conflicts:") {
                        ks_conflicts = rest.split_whitespace().next()
                            .and_then(|t| t.parse().ok());
                    } else if let Some(rest) = line.strip_prefix("c restarts:") {
                        ks_restarts = rest.split_whitespace().next()
                            .and_then(|t| t.parse().ok());
                    } else if verdict.is_none() && is_report(&line) {
                        last_report = Some(line.clone());
                        if args.show_progress && last.elapsed().as_secs_f64() >= 0.4 {
                            last = Instant::now();
                            eprintln!("c {}: {} {}", bk, engine_name,
                                      line.trim_start_matches('c').trim());
                        }
                    }
                }
            }
            let _ = child.wait();
            if verdict.is_some() {
                break;
            }
            // Phase timed out: discard any partial DRAT before the next one.
            let _ = std::fs::remove_file(&drat_tmp);
        }
        eprintln!("c {}: prover={}", bk,
                  if deciding_kissat { "kissat" } else { "cadical" });
        // Conflicts + restarts from CaDiCaL's last report row (column order:
        // marker seconds MB level reduction RESTARTS rate CONFLICTS …) emitted
        // as a line run_benchmark scrapes for its conflicts/restarts columns.
        if deciding_kissat {
            if let (Some(c), Some(r)) = (ks_conflicts, ks_restarts) {
                eprintln!("c {}: stats conflicts={} restarts={}", bk, c, r);
            }
        } else if let Some(row) = last_report.as_deref() {
            // CaDiCaL has no clean stat lines; scrape its last report row
            // (column positions are CaDiCaL-specific).
            let f: Vec<&str> = row.trim_start_matches("c ").split_whitespace().collect();
            if f.len() >= 8 {
                if let (Ok(restarts), Ok(conflicts)) =
                    (f[5].parse::<u64>(), f[7].parse::<u64>())
                {
                    eprintln!("c {}: stats conflicts={} restarts={}", bk,
                              conflicts, restarts);
                }
            }
        }
        // Standard timing line (stderr) so run_benchmark's parser records
        // the time; the verdict comes from the relayed `s` line on stdout.
        let el_ms = t0.elapsed().as_secs_f64() * 1000.0;
        match verdict.as_deref() {
            Some("UNSATISFIABLE") => {
                eprintln!("c UNSAT in {:.1}ms", el_ms);
                verdict_done.store(true, std::sync::atomic::Ordering::Relaxed);
                if emit_lrat {
                    if deciding_kissat {
                        // Elaborate kissat's binary DRAT into a GRAT
                        // certificate with gratgen (parallel; ~2x faster than
                        // drat-trim and far lighter on the verified checker via
                        // gratchk).  The solve timing above is already printed,
                        // so this elaboration is not charged to the solve time.
                        if let Some(out) = args.proof.as_ref() {
                            let gratgen = [
                                "/opt/homebrew/bin/gratgen", "/usr/local/bin/gratgen",
                            ].iter().find(|p| std::path::Path::new(p).exists()).copied()
                                .map(str::to_string)
                                .unwrap_or_else(|| {
                                    let home = std::env::var("HOME").unwrap_or_default();
                                    let c = format!("{}/.cargo/bin/gratgen", home);
                                    if std::path::Path::new(&c).exists() { c }
                                    else { "gratgen".to_string() }
                                });
                            let t_e = Instant::now();
                            let elab_deadline = if args.elab_time_s > 0 {
                                args.elab_time_s
                            } else if args.timeout_secs > 0 {
                                args.timeout_secs
                            } else {
                                0
                            };
                            let drat_mb = std::fs::metadata(&drat_tmp)
                                .map(|m| m.len()).unwrap_or(0) as f64 / 1e6;
                            // gratgen writes the GRAT to the -o file and prints
                            // its verdict ("s VERIFIED") + stats to STDERR (not
                            // stdout); capture stderr to a temp file
                            // (deadlock-safe) and read it back for the marker.
                            // --no-progress-bar: we drive our own elapsed/size
                            // ticks from the poll below.
                            let elog = std::env::temp_dir().join(
                                format!("pbcadical-{}.elog", std::process::id()));
                            let mut ecmd = std::process::Command::new(&gratgen);
                            // gratgen takes OPTIONS AFTER the positionals;
                            // -b reads the binary DRAT, -o writes combined GRAT.
                            ecmd.arg(&tmp).arg(&drat_tmp)
                                .arg("-b").arg("-o").arg(out)
                                .arg("-j").arg(args.elab_jobs.to_string())
                                .arg("--no-progress-bar");
                            ecmd.stdout(std::process::Stdio::null());
                            ecmd.stderr(std::fs::File::create(&elog)
                                .map(std::process::Stdio::from)
                                .unwrap_or_else(|_| std::process::Stdio::null()));
                            let mut reported_fail = false;
                            let ok = match ecmd.spawn() {
                                Ok(mut ch) => {
                                    let mut last = Instant::now();
                                    loop {
                                        match ch.try_wait() {
                                            Ok(Some(_)) => break,
                                            Ok(None) => {
                                                if elab_deadline > 0
                                                    && t_e.elapsed().as_secs() > elab_deadline
                                                {
                                                    eprintln!("c {}: gratgen elaboration \
                                                               TIMEOUT ({}s); no proof",
                                                              bk, elab_deadline);
                                                    let _ = ch.kill();
                                                    let _ = ch.wait();
                                                    reported_fail = true;
                                                    break;
                                                }
                                                if last.elapsed().as_secs_f64() >= 5.0 {
                                                    last = Instant::now();
                                                    // RSS guard: gratgen is
                                                    // otherwise unbounded and can
                                                    // take down the machine.
                                                    if args.elab_mem_mb > 0 {
                                                        let rss_mb = std::process::Command::new("ps")
                                                            .args(["-o", "rss=", "-p",
                                                                   &ch.id().to_string()])
                                                            .output().ok()
                                                            .and_then(|o| String::from_utf8_lossy(&o.stdout)
                                                                .trim().parse::<u64>().ok())
                                                            .map(|kb| kb / 1024)
                                                            .unwrap_or(0);
                                                        if rss_mb > args.elab_mem_mb {
                                                            eprintln!("c {}: gratgen elaboration \
                                                                       MEMOUT (>{}MB); no proof",
                                                                      bk, args.elab_mem_mb);
                                                            let _ = ch.kill();
                                                            let _ = ch.wait();
                                                            reported_fail = true;
                                                            break;
                                                        }
                                                    }
                                                    if args.show_progress {
                                                        let gmb = std::fs::metadata(out)
                                                            .map(|m| m.len()).unwrap_or(0)
                                                            as f64 / 1e6;
                                                        eprintln!("c {}: elaborating DRAT -> GRAT… \
                                                                   {:.0}s (drat {:.0}MB, grat {:.0}MB, \
                                                                   -j{})", bk,
                                                                  t_e.elapsed().as_secs_f64(),
                                                                  drat_mb, gmb, args.elab_jobs);
                                                    }
                                                }
                                                std::thread::sleep(
                                                    std::time::Duration::from_millis(500));
                                            }
                                            Err(_) => break,
                                        }
                                    }
                                    std::fs::read_to_string(&elog)
                                        .map(|t| t.contains("s VERIFIED"))
                                        .unwrap_or(false)
                                }
                                Err(e) => {
                                    eprintln!("c {}: gratgen spawn failed: {}", bk, e);
                                    reported_fail = true;
                                    false
                                }
                            };
                            let _ = std::fs::remove_file(&elog);
                            if ok {
                                eprintln!("c {}: proof-format=grat", bk);
                                eprintln!("c {}: kissat UNSAT; DRAT elaborated to GRAT at {} \
                                           ({:.1}s)", bk, out.display(),
                                          t_e.elapsed().as_secs_f64());
                            } else {
                                if !reported_fail {
                                    eprintln!("c {}: gratgen elaboration FAILED; no proof", bk);
                                }
                                let _ = std::fs::remove_file(out);
                            }
                        }
                    } else if let Some(out) = args.proof.as_ref() {
                        eprintln!("c {}: cadical UNSAT; LRAT proof at {}", bk, out.display());
                    }
                }
            }
            Some("SATISFIABLE") => {
                eprintln!("c SAT in {:.1}ms", el_ms);
                verdict_done.store(true, std::sync::atomic::Ordering::Relaxed);
                eprintln!("c {}: {} SAT (model is the certificate; \
                           no refutation proof)", bk,
                          if deciding_kissat { "kissat" } else { "cadical" });
                if let Some(out) = args.proof.as_ref() { let _ = std::fs::remove_file(out); }
                if reconstruct_model {
                    // Reconstruct the ORIGINAL formula's model from the
                    // engine's assignment over the transformed formula: keep
                    // only original variables (aux SBP vars > nvars are
                    // dropped), and — for a GE residual — overwrite every
                    // GE-forced var with its forced value (those were
                    // eliminated, so the engine's values are arbitrary). Sound
                    // because SBPs only remove models: the projection of any
                    // augmented model is a genuine original model.
                    let mut sign = vec![true; nvars + 1];
                    for &l in &vline {
                        let v = l.unsigned_abs() as usize;
                        if v <= nvars { sign[v] = l > 0; }
                    }
                    if let Some(f) = forced {
                        for (i, ov) in f.iter().enumerate() {
                            if let Some(b) = ov {
                                if i + 1 <= nvars { sign[i + 1] = *b; }
                            }
                        }
                    }
                    let mut line = String::from("v");
                    for v in 1..=nvars {
                        line.push(' ');
                        if !sign[v] { line.push('-'); }
                        line.push_str(&v.to_string());
                        if line.len() > 70 {
                            println!("{}", line);
                            line = String::from("v");
                        }
                    }
                    println!("{} 0", line);
                }
            }
            _ => {
                eprintln!("c TIMEOUT after {:.1}ms", el_ms);
                verdict_done.store(true, std::sync::atomic::Ordering::Relaxed);
                eprintln!("c {}: {} reached no verdict (timeout/unknown)", bk,
                          if deciding_kissat { "kissat" } else { "cadical" });
            }
        }
        let _ = std::fs::remove_file(&tmp);
        let _ = std::fs::remove_file(&drat_tmp);
        return;
    }

    // Quick edge cases handled before invoking either backend.  We
    // still emit the standard `c UNSAT|SAT in 0.0ms` timing line on
    // these fast paths so downstream consumers (the
    // doc/competition-benchmarks.sh parser, etc.) get a uniform
    // result format regardless of which path the solver took.
    if clauses.iter().any(|c| c.is_empty()) {
        eprintln!("c UNSAT in 0.0ms");
        println!("s UNSATISFIABLE");
        return;
    }
    if clauses.is_empty() {
        eprintln!("c SAT in 0.0ms");
        println!("s SATISFIABLE");
        let stdout = io::stdout();
        let mut w = stdout.lock();
        write_v_line(&mut w, &vec![true; nvars]).unwrap();
        return;
    }

    eprintln!("c backend: {}", args.backend.name());
    // CaDiCaL runs its own inprocessing; the matrix-method `--preprocess`
    // pass is never applied to it (the gate lives in the Matrix arm
    // below).  Say so explicitly so it's clear from the log that a
    // cadical run does NO NNF preprocessing, regardless of the
    // (ignored) --preprocess flag.
    if matches!(args.backend, BackendChoice::Cadical) {
        eprintln!("c preprocess: n/a (CaDiCaL backend runs its own inprocessing)");
    }
    // Only log eff-tau when it's been changed from the default —
    // keeps the banner unchanged for the common case so existing
    // log parsers don't trip over a new line.
    if args.eff_tau != 0.0 {
        eprintln!("c eff-tau: {} (variance-gated Sum reordering)", args.eff_tau);
    }
    if args.timeout_secs > 0 {
        eprintln!("c timeout: {}s", args.timeout_secs);
        // Spawn a watcher thread that hard-exits the process after
        // the wall-clock budget is reached.  This is independent of
        // the search engine's own cancellation paths and works for
        // all backends (single-DFS, dual, CaDiCaL).  The watcher
        // calls `restore_terminal()` before exit so the cursor
        // stays sane when `--progress` was used.
        let limit = args.timeout_secs;
        std::thread::spawn(move || {
            std::thread::sleep(std::time::Duration::from_secs(limit));
            restore_terminal();
            // Stats first (so the canonical line is present before
            // the timeout marker), then the human-readable timeout
            // line.  Both go to stderr.  `print_stats_line` is
            // idempotent: if the normal-completion path raced ahead
            // and already printed, this call is a no-op.
            print_stats_line();
            eprintln!("\nc TIMEOUT after {}s", limit);
            // 124 is the standard GNU `timeout` exit code.
            std::process::exit(124);
        });
    }

    // XOR-recovery + GF(2) Gaussian-elimination pre-pass (matrix
    // backends only — CaDiCaL does its own).  Parity/XOR-structured
    // formulas (random mod-2 systems, Urquhart, the x1/x2 family) are
    // exponential for resolution, hence for the matrix search, but
    // LINEAR over GF(2).  When the pass decides the formula, skip the
    // search entirely.
    // Holds the GE-derived forced assignment when the pass simplifies a
    // mixed formula: the matrix search runs on the residual (which no
    // longer mentions the forced vars), so on SAT we must overlay these
    // constants back onto the search's model before printing it.
    let mut xor_forced: Option<Vec<Option<bool>>> = None;

    // Structure-based visit-order routing for eff backends.  Detect an
    // "exactly-one" cardinality CSP (PHP / RoundRobin / MVRoundRobin /
    // scheduling) on the ORIGINAL clauses and, if found, force pure
    // EffectiveCount ordering — the matrix path-count heuristic dominates
    // these symmetric instances, and the default VSIDS-alternating
    // portfolio only wastes half its restart epochs there (it regressed 5
    // RoundRobin instances on the main track).  An explicit `EFF_VSIDS`
    // env override (for experiments) always wins.
    let eff_vsids_override: Option<u8> =
        if std::env::var("EFF_VSIDS").is_ok() {
            None
        } else if matches!(args.backend, BackendChoice::Matrix(_))
            && logic::cook_pbp::is_exactly_one_csp(&clauses)
        {
            eprintln!("c structure: exactly-one CSP (PHP/RoundRobin-like) \
                       — using EffectiveCount ordering (no VSIDS alternation)");
            Some(0)
        } else {
            None
        };

    let xg_cap = args.xor_gauss_max_clauses;
    let xg_ok = xg_cap == 0 || clauses.len() <= xg_cap;
    if args.xor_gauss && !xg_ok {
        eprintln!("c xor-gauss: auto-skipped ({} clauses > {} cap; raise with \
                   --xor-gauss-max-clauses N (0=unlimited) or silence with --no-xor-gauss)",
                  clauses.len(), xg_cap);
    }
    if args.xor_gauss && xg_ok && matches!(args.backend, BackendChoice::Matrix(_)) {
        let t_xg = Instant::now();
        match logic::xor_gauss::solve_xor_system(nvars, &clauses, 50_000_000) {
            logic::xor_gauss::XorGaussResult::Unsat { by_bcp } => {
                let _ = by_bcp;
                let ms = t_xg.elapsed().as_secs_f64() * 1000.0;
                eprintln!("c xor-gauss: recovered XOR system is inconsistent");
                eprintln!("c UNSAT in {:.1}ms", ms);
                println!("s UNSATISFIABLE");
                return;
            }
            logic::xor_gauss::XorGaussResult::Sat(model) => {
                let ms = t_xg.elapsed().as_secs_f64() * 1000.0;
                eprintln!("c xor-gauss: pure-XOR formula solved by Gaussian elimination");
                eprintln!("c SAT in {:.1}ms", ms);
                println!("s SATISFIABLE");
                let stdout = io::stdout();
                let mut w = stdout.lock();
                write_v_line(&mut w, &model).unwrap();
                return;
            }
            logic::xor_gauss::XorGaussResult::Simplified { clauses: residual, forced, recovered, forced_count } => {
                let ms = t_xg.elapsed().as_secs_f64() * 1000.0;
                eprintln!("c xor-gauss: recovered {} XOR(s); GE + BCP forced {} var(s), \
                           residual {} clause(s) (from {}) in {:.1}ms — searching the residual",
                          recovered, forced_count, residual.len(), clauses.len(), ms);
                clauses = residual;
                xor_forced = Some(forced);
            }
            logic::xor_gauss::XorGaussResult::Indeterminate { recovered, consumed, total } => {
                if recovered > 0 {
                    eprintln!("c xor-gauss: recovered {} XOR(s) covering {}/{} clauses; \
                               formula is mixed — running the matrix search on the rest",
                              recovered, consumed, total);
                }
            }
        }
    }

    let t = Instant::now();
    let outcome = match args.backend {
        BackendChoice::Cadical => cadical_search(nvars, clauses, args.show_progress),
        BackendChoice::PbCadical => unreachable!("pb-cadical is handled before the search dispatch"),
        BackendChoice::Hydra | BackendChoice::HydraSymBreak | BackendChoice::HydraSatsuma
        | BackendChoice::Satsuma =>
            unreachable!("hydra is handled before the search dispatch"),
        BackendChoice::Matrix(m) => {
            // Auto-skip preprocess on very large inputs.  Empirically
            // Phase 1 preprocess takes ~150 µs / clause; at 2M
            // clauses (pj2013_k9) that's ~5 minutes — most of any
            // reasonable per-problem budget before the matrix search
            // even starts.  The cap is configurable via
            // `--preprocess-max-clauses N` (0 = no cap); default 250k
            // (≈38 s).  Users wanting preprocess off entirely pass
            // `--no-preprocess`.
            let cap = args.preprocess_max_clauses;
            let do_preprocess = args.preprocess
                && (cap == 0 || clauses.len() <= cap);
            if args.preprocess && !do_preprocess {
                eprintln!("c preprocess: auto-skipped ({} clauses > {} cap; \
                           raise with --preprocess-max-clauses N (0=unlimited) \
                           or silence with --no-preprocess)",
                          clauses.len(), cap);
            }
            if do_preprocess {
                // Build F as NNF (Prod-of-Sums), run NNF-level
                // preprocessing (UP / BVE / normalisation), check
                // for a fully-resolved result, otherwise hand the
                // complement of the simplified NNF to the matrix
                // search.  See `src/preprocess.rs` for the pipeline
                // and `doc/preprocess.md` for the design rationale.
                let orig_clauses = clauses.len();
                let f = cnf_to_nnf(&clauses);
                drop(clauses);
                let pp_start = Instant::now();
                let pp = logic::preprocess::preprocess(&f);
                let pp_ms = pp_start.elapsed().as_secs_f64() * 1000.0;
                drop(f);
                // Top-level clause count after preprocessing — Phase
                // 1 keeps CNF shape (Prod-of-Sums), so this is just
                // the root Prod's child count.  Useful to see at a
                // glance whether preprocess actually shrunk the
                // formula on a given input.
                let pp_clauses = match &pp.nnf {
                    NNF::Prod(ch) => ch.len(),
                    NNF::Sum(_)   => 0,   // trivially unsat
                    NNF::Lit(_)   => 1,   // single forced lit
                };
                let delta_pct = if orig_clauses == 0 { 0 } else {
                    (pp_clauses as i64 - orig_clauses as i64) * 100
                     / orig_clauses as i64
                };
                eprintln!("c preprocess: {} → {} clauses ({:+}%) in {:.1}ms",
                          orig_clauses, pp_clauses, delta_pct, pp_ms);
                match preprocess_verdict(&pp.nnf) {
                    PreprocessVerdict::TriviallySat => {
                        // Preprocessor reduced F to true (the empty
                        // Prod).  Build a SAT model from the
                        // reconstruction stack only (every survivor
                        // defaults to false; recon steps then fill
                        // in any forced lits in reverse order).
                        let mut asgn_lits: Vec<Lit> = Vec::new();
                        pp.pad_survivors_and_extend(&mut asgn_lits, nvars as u32);
                        let mut bool_asgn = vec![true; nvars];
                        for l in &asgn_lits {
                            if (l.var as usize) < nvars {
                                bool_asgn[l.var as usize] = !l.neg;
                            }
                        }
                        SearchOutcome::Sat(bool_asgn)
                    }
                    PreprocessVerdict::TriviallyUnsat => {
                        SearchOutcome::Unsat
                    }
                    PreprocessVerdict::NeedsSearch => {
                        let comp = pp.nnf.complement();
                        // Preprocess+cover: --emit-cover with
                        // --preprocess isn't currently supported
                        // because positions reference the preprocessed
                        // CNF, not the input.  matrix_search will
                        // panic loudly if both are set.
                        // Preprocess path: --emit-pbp is rejected
                        // earlier (variables would be shifted).
                        // Pass 0 as n_input_clauses since it's unused.
                        matrix_search(comp, nvars, args.show_progress, m,
                                      Some(&pp), args.emit_cover.as_deref(),
                                      None,
                                      args.emit_drat.as_deref(),
                                      args.emit_pbp.as_deref(),
                                      0,
                                      args.timeout_secs,
                                      args.eff_tau, eff_vsids_override)
                    }
                }
            } else {
                // Skip preprocess: build the complement directly
                // and search it.  When --emit-cover is set, keep
                // `clauses` alive (Arc'd inside CoverWriter for
                // position-to-lit resolution); otherwise drop the
                // parsed clauses before the search starts (≈ 80 MB
                // on 2M-clause inputs).
                let n_clauses = clauses.len();
                let comp = cnf_complement_nnf(&clauses);
                if args.emit_cover.is_some() {
                    let cover_clauses = clauses.clone();
                    drop(clauses);
                    matrix_search(comp, nvars, args.show_progress, m, None,
                                  args.emit_cover.as_deref(),
                                  Some(&cover_clauses),
                                  args.emit_drat.as_deref(),
                                  args.emit_pbp.as_deref(),
                                  n_clauses,
                                  args.timeout_secs,
                                  args.eff_tau, eff_vsids_override)
                } else {
                    drop(clauses);
                    matrix_search(comp, nvars, args.show_progress, m, None,
                                  args.emit_cover.as_deref(),
                                  None,
                                  args.emit_drat.as_deref(),
                                  args.emit_pbp.as_deref(),
                                  n_clauses,
                                  args.timeout_secs,
                                  args.eff_tau, eff_vsids_override)
                }
            }
        }
    };
    let elapsed_ms = t.elapsed().as_secs_f64() * 1000.0;

    // A live progress display renders with a leading `\r` and NO
    // trailing newline, so when the search finishes the cursor is left
    // mid-line.  Terminate that line before printing the verdict —
    // otherwise the verdict gets glued onto the last progress frame
    // (e.g. `c CaDiCaL: … 0.2sc UNSAT in 260ms`) and a line-anchored
    // parser like run_benchmark's can't match `^c (SAT|UNSAT) in …`,
    // reporting UNKNOWN for a problem that was actually solved.  (The
    // TIMEOUT path already leads with `\n` for exactly this reason.)
    if args.show_progress {
        eprintln!();
    }

    match outcome {
        SearchOutcome::Unsat => {
            eprintln!("c UNSAT in {:.1}ms", elapsed_ms);
            println!("s UNSATISFIABLE");
        }
        SearchOutcome::Sat(mut asgn) => {
            eprintln!("c SAT in {:.1}ms", elapsed_ms);
            println!("s SATISFIABLE");
            // Overlay XOR-GE forced constants: the residual the search
            // saw no longer mentioned these vars, so its model left them
            // at arbitrary defaults. Restore the GE/BCP-derived values so
            // the printed witness satisfies the *original* formula.
            if let Some(forced) = &xor_forced {
                for (i, f) in forced.iter().enumerate() {
                    if let (Some(b), Some(slot)) = (f, asgn.get_mut(i)) {
                        *slot = *b;
                    }
                }
            }
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
        match matrix_search(comp, nvars, /*show_progress=*/ false, backend, None, None, None, None, None, 0, 0, 0.0, None) {
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
        // log_total=0 and start≈now) shouldn't panic or divide-by-zero.
        // Output goes to stderr, which captures during tests.
        //   (so_far, max_so_far, log_total, elapsed_secs, timeout_secs, frame, conflicts, restarts)
        // ---- both bars (timeout_secs > 0) ----
        render_progress(0.0,   0.0,   0.0,  0.0,  60, 0, 0, 0);   // pre-progress
        render_progress(50.0,  50.0,  4.0,  1.5,  60, 1, 0, 0);   // so_far=max=50
        render_progress(1e6,   1e6,   8.0,  12.3, 60, 2, 0, 0);   // mid run
        render_progress(1e15,  1e15,  15.0, 30.0, 60, 3, 0, 0);   // late
        render_progress(1e9,   1e9,   3.0,  1.0,  60, 4, 0, 0);   // so_far > total: clamp
        // ---- post-restart: so_far < max_so_far → marker visible ----
        render_progress(1e4,   1e8,   10.0, 5.0,  60, 5, 0, 0);
        render_progress(0.0,   1e8,   10.0, 5.0,  60, 6, 0, 0);   // current reset to 0
        // ---- log_total = -inf (formula has 0 paths; degenerate) ----
        render_progress(0.0, 0.0, f64::NEG_INFINITY, 0.5, 60, 7, 0, 0);
        // ---- log_total = inf (shouldn't happen, but be defensive) ----
        render_progress(100.0, 100.0, f64::INFINITY, 1.0, 60, 8, 0, 0);
        // ---- single bar only (timeout_secs == 0) ----
        render_progress(0.0,   0.0,  0.0,  0.0,  0, 0, 0, 0);
        render_progress(50.0,  50.0, 4.0,  1.5,  0, 1, 0, 0);
        // ---- with CDCL stats (greedy_cdcl / greedy_eff on hard UNSAT) ----
        render_progress(0.0,   0.0,   180.0, 5.0,  60, 9,  1234, 5);
        render_progress(1e150, 1e150, 180.0, 30.0, 60, 10, 999_999, 42);
    }

    #[test]
    fn format_log_count_handles_edges() {
        assert_eq!(format_log_count(f64::NEG_INFINITY), "0");
        assert_eq!(format_log_count(f64::INFINITY),     "?");
        assert_eq!(format_log_count(f64::NAN),          "?");
        // log10(1) = 0 → "1"
        assert_eq!(format_log_count(0.0), "1");
        // log10(1000) = 3 → "1.0K"
        assert_eq!(format_log_count(3.0), "1.0K");
        // log10(1e8) = 8 → "100.0M"  (still under 1e9 threshold)
        let s = format_log_count(8.0);
        assert!(s.ends_with("M"), "expected M-suffix for log=8, got {}", s);
        // log10(1e10) = 10 → "10^10.0"
        assert_eq!(format_log_count(10.0), "10^10.0");
        // Very large: log10 = 4500 → "10^4500.0"
        assert_eq!(format_log_count(4500.0), "10^4500.0");
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
            MatrixBackend::BasicEff,
        ] {
            match matrix_search(cnf_complement_nnf(&[vec![1, -2], vec![2, 3], vec![-1, -3]]), 3, false, backend, None, None, None, None, None, 0, 0, 0.0, None) {
                SearchOutcome::Sat(_) => {}
                other => panic!("[{:?}] expected Sat, got {:?}", backend, outcome_kind(&other)),
            }
            match matrix_search(cnf_complement_nnf(&[vec![1], vec![-1]]), 1, false, backend, None, None, None, None, None, 0, 0, 0.0, None) {
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

    /// Single-line case: a small assignment fits in one `v` line with
    /// the `0` terminator.  Each lit is rendered with the right sign;
    /// variables are 1-based DIMACS.
    #[test]
    fn write_v_line_small_fits_on_one_line() {
        let mut buf: Vec<u8> = Vec::new();
        // asgn = [true, false, true] → vars 1, -2, 3
        write_v_line(&mut buf, &[true, false, true]).unwrap();
        let s = std::str::from_utf8(&buf).unwrap();
        assert_eq!(s, "v 1 -2 3 0\n");
    }

    /// Empty assignment edge case: just `v 0\n` (the spec allows
    /// partial assignments, so an empty one is degenerate-valid).
    #[test]
    fn write_v_line_empty_assignment() {
        let mut buf: Vec<u8> = Vec::new();
        write_v_line(&mut buf, &[]).unwrap();
        assert_eq!(std::str::from_utf8(&buf).unwrap(), "v 0\n");
    }

    /// Multi-line case: a large assignment splits across multiple
    /// `v ` lines, each ≤ 4096 chars including the trailing newline,
    /// with only the very last line carrying the `0` terminator.
    /// 1500 vars × ~5 chars/lit ≈ 7.5 KB → must wrap at least once.
    #[test]
    fn write_v_line_wraps_at_4096() {
        let nvars = 1500;
        let asgn: Vec<bool> = (0..nvars).map(|i| i % 2 == 0).collect();
        let mut buf: Vec<u8> = Vec::new();
        write_v_line(&mut buf, &asgn).unwrap();
        let s = std::str::from_utf8(&buf).unwrap();

        // Every line must start with `v ` and be ≤ 4096 chars
        // (including the newline).
        let lines: Vec<&str> = s.lines().collect();
        assert!(lines.len() >= 2,
            "expected multi-line output for {} vars, got {} lines",
            nvars, lines.len());
        for line in &lines {
            assert!(line.starts_with("v "),
                "value line must start with 'v ': {:?}", line);
            assert!(line.len() + 1 <= 4096,  // +1 for the \n
                "value line exceeds 4096 chars (got {}): {}", line.len() + 1, line);
        }

        // Only the last line carries the ` 0` terminator.
        assert!(lines.last().unwrap().ends_with(" 0"),
            "last line must end with ' 0': {:?}", lines.last().unwrap());
        for line in &lines[..lines.len() - 1] {
            assert!(!line.ends_with(" 0"),
                "non-final value line must not have ' 0' terminator: {:?}", line);
        }

        // Round-trip: collect all literals across every line and
        // confirm we got exactly the right ones in order.  Skip the
        // leading "v" token on each line and the trailing "0" on the
        // last line.
        let mut lits: Vec<i32> = Vec::new();
        for line in &lines {
            for tok in line.split_ascii_whitespace().skip(1) {
                if tok == "0" { continue; }
                lits.push(tok.parse().unwrap());
            }
        }
        assert_eq!(lits.len(), nvars);
        for (i, &lit) in lits.iter().enumerate() {
            let expected = (i as i32 + 1) * if asgn[i] { 1 } else { -1 };
            assert_eq!(lit, expected, "lit at position {}", i);
        }
    }
}
