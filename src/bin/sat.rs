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
use std::sync::atomic::{AtomicU8, Ordering};

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
        && !matches!(backend, MatrixBackend::Cdcl | MatrixBackend::Smart)
    {
        eprintln!("c ERROR: --emit-cover only supported with backend cdcl or smart \
                   (got {}); other backends use the positions-OFF or arena engine \
                   which doesn't track the positional info the cert format needs",
                  backend.name());
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
                        ctrl.drat_hook = drat_for_search;
                        ctrl
                    })
                } else {
                    comp.classify_paths_uncovered_only(64,
                        move |tx| cdcl_controller_builder(&nnf_cdcl, p_cdcl, tx),
                    )
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
                    let cdcl = CdclController::for_arena_with_cover(arena_ref, p_eff, on_class);
                    let idx = EffectiveCountIndex::build_from_arena(arena_ref);
                    let counts = EffectiveCounts::new(&idx);
                    EffectiveCountWrapper::new_with_tau(cdcl, idx, counts, tau)
                };
                if matches!(backend, MatrixBackend::Effb) {
                    arena.classify_paths_with_arena_bubble_up(64, builder)
                } else {
                    arena.classify_paths_with_arena(64, builder)
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
            _ => Err(format!(
                "unknown backend {:?}; expected one of: smart, cdcl, eff, effb, \
                 greedy_cdcl, greedy_eff, greedy_effb, basic_eff, basic_effb, cadical", s
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

fn parse_args() -> Result<Args, String> {
    let mut a = Args {
        show_progress: false,
        backend: BackendChoice::Matrix(MatrixBackend::Eff),
        timeout_secs: DEFAULT_TIMEOUT_SECS,
        preprocess: true,
        emit_cover: None,
        emit_drat: None,
        emit_pbp: None,
        emit_cook_pbp: None,
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
    let (nvars, clauses) = match parse_dimacs(stdin.lock()) {
        Ok(x) => x,
        Err(e) => {
            eprintln!("c parse error: {}", e);
            std::process::exit(1);
        }
    };
    eprintln!("c parsed {} variables, {} clauses", nvars, clauses.len());

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
            eprintln!("\nc TIMEOUT after {}s", limit);
            // 124 is the standard GNU `timeout` exit code.
            std::process::exit(124);
        });
    }
    let t = Instant::now();
    let outcome = match args.backend {
        BackendChoice::Cadical => cadical_search(nvars, clauses, args.show_progress),
        BackendChoice::Matrix(m) => {
            // Auto-skip preprocess on very large inputs.  Empirically
            // Phase 1 preprocess takes ~150 µs / clause; at 2M
            // clauses (pj2013_k9) that's ~5 minutes — most of any
            // reasonable per-problem budget before the matrix
            // search even starts.  Auto-skip above 250k clauses.
            // Users wanting preprocess off entirely should pass
            // `--no-preprocess`; users wanting it on for giant
            // inputs (rare, niche) can bump the threshold by
            // editing this constant.
            //
            // Threshold rationale: 250k × 150 µs ≈ 38 seconds —
            // acceptable fraction of a 600 s budget but a clear
            // "too long" for 60 s benchmarking.
            const PREPROCESS_MAX_CLAUSES: usize = 250_000;
            let do_preprocess = args.preprocess
                && clauses.len() <= PREPROCESS_MAX_CLAUSES;
            if args.preprocess && !do_preprocess {
                eprintln!("c preprocess: auto-skipped ({} clauses > {} \
                           threshold; use --no-preprocess to silence)",
                          clauses.len(), PREPROCESS_MAX_CLAUSES);
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
                                      args.eff_tau)
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
                                  args.eff_tau)
                } else {
                    drop(clauses);
                    matrix_search(comp, nvars, args.show_progress, m, None,
                                  args.emit_cover.as_deref(),
                                  None,
                                  args.emit_drat.as_deref(),
                                  args.emit_pbp.as_deref(),
                                  n_clauses,
                                  args.timeout_secs,
                                  args.eff_tau)
                }
            }
        }
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
        match matrix_search(comp, nvars, /*show_progress=*/ false, backend, None, None, None, None, None, 0, 0, 0.0) {
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
            match matrix_search(cnf_complement_nnf(&[vec![1, -2], vec![2, 3], vec![-1, -3]]), 3, false, backend, None, None, None, None, None, 0, 0, 0.0) {
                SearchOutcome::Sat(_) => {}
                other => panic!("[{:?}] expected Sat, got {:?}", backend, outcome_kind(&other)),
            }
            match matrix_search(cnf_complement_nnf(&[vec![1], vec![-1]]), 1, false, backend, None, None, None, None, None, 0, 0, 0.0) {
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
