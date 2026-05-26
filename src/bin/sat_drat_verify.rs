//! `sat-drat-verify` — independent verifier for DRAT UNSAT proofs
//! emitted by `sat --emit-drat FILE`.
//!
//! # Background
//!
//! DRAT (Delete Resolution Asymmetric Tautology) is the SAT-competition
//! standard proof format.  A DRAT proof is a sequence of clauses, one
//! per line in DIMACS form (`<lit1> <lit2> ... 0`), optionally
//! prefixed by `d` for clause deletion.  The proof terminates with the
//! empty clause `0` (UNSAT).
//!
//! Soundness condition (RUP variant — DRUP):
//!
//! > Each added clause C must be *RUP-implied* by the current clause
//! > set: unit-propagation on `(clauses ∪ {¬l for l in C})` reaches a
//! > conflict (the empty clause).
//!
//! Verification is straightforward: maintain the clause DB with
//! watched literals; for each proof clause, assume each lit's
//! negation as a unit, propagate, expect conflict.
//!
//! Full DRAT also has RAT (Resolution Asymmetric Tautology) for
//! clauses where RUP doesn't suffice but the clause is "RAT on
//! some pivot lit".  This verifier currently checks **only RUP**
//! (= DRUP).  All clauses emitted by our cdcl backend are
//! 1UIP-derived resolvents → RUP-implied → DRUP suffices.  If the
//! emitter ever adds non-RUP DRAT steps (e.g., blocked-clause
//! addition), extend this verifier with the RAT check.
//!
//! # CLI
//!
//! ```text
//! sat-drat-verify <cnf-file> <drat-file>
//! ```
//!
//! Exits 0 on `VALID UNSAT PROOF`, 1 on invalid proof,
//! 2 on usage / I/O error.

use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::ExitCode;

// ─── DIMACS parsing ─────────────────────────────────────────────────────────

/// `Lit` is a signed DIMACS int packed as `usize`: `2*var + neg`
/// (var is 1-indexed).  Indexed encoding makes watch-list lookups
/// O(1) without HashMap overhead.
type LitCode = usize;

fn lit_code(dimacs: i32) -> LitCode {
    let v = dimacs.unsigned_abs() as usize;
    v * 2 + if dimacs < 0 { 1 } else { 0 }
}
fn lit_neg(code: LitCode) -> LitCode { code ^ 1 }
fn lit_var(code: LitCode) -> usize { code / 2 }
fn lit_is_neg(code: LitCode) -> bool { code & 1 == 1 }
#[allow(dead_code)]
fn lit_to_dimacs(code: LitCode) -> i32 {
    let v = lit_var(code) as i32;
    if lit_is_neg(code) { -v } else { v }
}

#[derive(Debug)]
struct Cnf {
    nvars:   usize,
    clauses: Vec<Vec<LitCode>>,
}

fn parse_dimacs<R: BufRead>(r: R) -> Result<Cnf, String> {
    let mut nvars = 0;
    let mut clauses: Vec<Vec<LitCode>> = Vec::new();
    let mut current: Vec<LitCode> = Vec::new();
    for (lineno, line) in r.lines().enumerate() {
        let line = line.map_err(|e| format!("read error at line {}: {}", lineno + 1, e))?;
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') || t.starts_with('%') { continue; }
        if let Some(rest) = t.strip_prefix("p cnf ") {
            let mut it = rest.split_ascii_whitespace();
            if let Some(v) = it.next() {
                nvars = v.parse().map_err(|_|
                    format!("line {}: bad nvars in p cnf header", lineno + 1))?;
            }
            continue;
        }
        if t.starts_with("p ") { continue; }
        for tok in t.split_ascii_whitespace() {
            let n: i32 = tok.parse().map_err(|_|
                format!("line {}: not an integer: {:?}", lineno + 1, tok))?;
            if n == 0 {
                if !current.is_empty() {
                    clauses.push(std::mem::take(&mut current));
                }
            } else {
                current.push(lit_code(n));
            }
        }
    }
    if !current.is_empty() {
        clauses.push(current);
    }
    if nvars == 0 {
        nvars = clauses.iter()
            .flat_map(|c| c.iter())
            .map(|&l| lit_var(l))
            .max()
            .unwrap_or(0);
    }
    Ok(Cnf { nvars, clauses })
}

// ─── DRAT parsing (line-by-line) ────────────────────────────────────────────

/// One DRAT proof step.
#[derive(Debug)]
enum DratStep {
    /// Add a clause (must be RUP-implied by current set).
    Add(Vec<LitCode>),
    /// Delete a clause (no soundness check; advisory for the
    /// checker's clause DB to shrink).
    Delete(Vec<LitCode>),
    /// Empty clause: `0` alone on a line.  Conventionally marks
    /// proof end.  We treat reaching it as the success condition
    /// (and additionally verify it's RUP-implied, which should
    /// reduce to "current set is already UNSAT").
    Empty,
}

fn parse_drat<R: BufRead>(r: R) -> Result<Vec<DratStep>, String> {
    let mut steps = Vec::new();
    for (lineno, line) in r.lines().enumerate() {
        let line = line.map_err(|e| format!("drat read error line {}: {}", lineno + 1, e))?;
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') { continue; }
        let (is_delete, body) = if let Some(rest) = t.strip_prefix("d ") {
            (true, rest)
        } else if t == "d" {
            (true, "")
        } else {
            (false, t)
        };
        let mut lits: Vec<LitCode> = Vec::new();
        let mut saw_zero = false;
        for tok in body.split_ascii_whitespace() {
            let n: i32 = tok.parse().map_err(|_|
                format!("drat line {}: not an integer: {:?}", lineno + 1, tok))?;
            if n == 0 {
                saw_zero = true;
                break;
            }
            lits.push(lit_code(n));
        }
        if !saw_zero {
            return Err(format!("drat line {}: clause not terminated by 0", lineno + 1));
        }
        if is_delete {
            steps.push(DratStep::Delete(lits));
        } else if lits.is_empty() {
            steps.push(DratStep::Empty);
        } else {
            steps.push(DratStep::Add(lits));
        }
    }
    Ok(steps)
}

// ─── RUP-checker with watched literals ──────────────────────────────────────

/// Three-valued assignment.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Val { Unassigned, True, False }

/// One clause in the DB.  `watches` are indices into `lits`
/// (always 0 and 1 for live clauses; we keep them as separate
/// fields for cache-friendliness).
struct Clause {
    lits: Vec<LitCode>,
    /// `true` once the clause has been deleted (DRAT `d` step).
    /// Deleted clauses get skipped by watch traversal.
    deleted: bool,
}

struct Checker {
    /// Variable count from the CNF header.  Used for sizing `value`
    /// and `watches` at construction; kept around for diagnostics.
    #[allow(dead_code)]
    nvars: usize,
    clauses: Vec<Clause>,
    /// `watches[lit_code]` = list of clause IDs that have `lit_code`
    /// as one of their two watched literals.  Indexed by lit_code
    /// (0..2*(nvars+1)).
    watches: Vec<Vec<usize>>,
    /// `value[var]` for var ∈ [1..=nvars].  value[0] unused.
    value: Vec<Val>,
    /// Trail of assigned lits (for unwinding the RUP check).
    trail: Vec<LitCode>,
    /// Index of next trail lit to propagate.
    qhead: usize,
}

impl Checker {
    fn new(nvars: usize) -> Self {
        let lit_max = (nvars + 1) * 2;
        Self {
            nvars,
            clauses: Vec::new(),
            watches: vec![Vec::new(); lit_max],
            value: vec![Val::Unassigned; nvars + 1],
            trail: Vec::new(),
            qhead: 0,
        }
    }

    /// Add a clause to the DB (assumes RUP-validity has been
    /// checked or doesn't need to be — original CNF clauses).
    ///
    /// Empty clauses → immediate UNSAT (`Err`).
    ///
    /// At level 0 (always, for proof checking), if the new clause
    /// is *currently unit* (exactly one Unassigned lit, all others
    /// False), we enqueue the implied lit so subsequent
    /// `propagate()` calls can find the conflict.  Without this,
    /// adding a unit clause `(¬a)` wouldn't put `a=False` on the
    /// trail and the empty-clause RUP check at proof end would
    /// silently fail.
    fn add_clause(&mut self, lits: Vec<LitCode>) -> Result<usize, ()> {
        let cid = self.clauses.len();
        if lits.is_empty() {
            self.clauses.push(Clause { lits, deleted: false });
            return Err(());   // immediate UNSAT
        }
        // Set up watches: pick two lits that aren't already False
        // (so the clause doesn't immediately re-trigger).  For
        // arity-1 clauses, watch the single lit.
        if lits.len() >= 2 {
            self.watches[lits[0]].push(cid);
            self.watches[lits[1]].push(cid);
        } else {
            self.watches[lits[0]].push(cid);
        }
        // Check current state: count Unassigned + False lits.
        let mut unassigned: Option<LitCode> = None;
        let mut already_true = false;
        let mut false_count = 0usize;
        for &l in &lits {
            match Self::lit_val_in(&self.value, l) {
                Val::True       => { already_true = true; break; }
                Val::False      => { false_count += 1; }
                Val::Unassigned => {
                    if unassigned.is_some() {
                        // More than one unassigned — clause is not
                        // currently unit; no enqueue needed.  Clear
                        // and bail out of the count loop.
                        unassigned = None;
                        false_count = usize::MAX;   // mark "not unit"
                        break;
                    }
                    unassigned = Some(l);
                }
            }
        }
        self.clauses.push(Clause { lits, deleted: false });
        if already_true {
            return Ok(cid);
        }
        // Determine if we need to enqueue or signal conflict.
        // - All False, no Unassigned: immediate empty clause →
        //   conflict.
        // - All False but one Unassigned: enqueue the survivor.
        // - Multiple Unassigned: nothing to do (watches will catch
        //   future conflicts).
        let n = self.clauses[cid].lits.len();
        if false_count == n {
            return Err(());
        }
        if let Some(l) = unassigned {
            if false_count == n - 1 {
                if self.enqueue(l).is_err() {
                    return Err(());
                }
            }
        }
        Ok(cid)
    }

    /// Delete a clause matching `lits` (set semantics — first match).
    /// Marks it deleted; watch lists still point at it but
    /// propagation skips deleted entries.
    fn delete_clause(&mut self, lits: &[LitCode]) {
        // Sort for comparison.
        let mut target: Vec<LitCode> = lits.to_vec();
        target.sort();
        for c in self.clauses.iter_mut() {
            if c.deleted { continue; }
            if c.lits.len() != target.len() { continue; }
            let mut sorted: Vec<LitCode> = c.lits.clone();
            sorted.sort();
            if sorted == target {
                c.deleted = true;
                return;
            }
        }
        // Silently ignore deletes for clauses we don't have —
        // matches drat-trim's behavior.
    }

    /// Value of a lit: True iff the lit is satisfied, False iff
    /// falsified, Unassigned otherwise.
    fn lit_val(&self, lit: LitCode) -> Val {
        Self::lit_val_in(&self.value, lit)
    }

    /// Same as `lit_val` but takes the value slice explicitly,
    /// so callers can use it inside an active `&mut self.clauses[..]`
    /// borrow without conflicting on `self`.
    fn lit_val_in(value: &[Val], lit: LitCode) -> Val {
        let v = lit_var(lit);
        let neg = lit_is_neg(lit);
        match value[v] {
            Val::Unassigned => Val::Unassigned,
            Val::True       => if neg { Val::False } else { Val::True },
            Val::False      => if neg { Val::True  } else { Val::False },
        }
    }

    /// Assign a lit to True (push on trail).  No-op if already
    /// True; conflict-signal if already False.
    fn enqueue(&mut self, lit: LitCode) -> Result<(), ()> {
        match self.lit_val(lit) {
            Val::True       => Ok(()),
            Val::False      => Err(()),
            Val::Unassigned => {
                let v = lit_var(lit);
                self.value[v] = if lit_is_neg(lit) { Val::False } else { Val::True };
                self.trail.push(lit);
                Ok(())
            }
        }
    }

    /// Unwind the trail back to the given length.
    fn backtrack_to(&mut self, len: usize) {
        while self.trail.len() > len {
            let l = self.trail.pop().unwrap();
            self.value[lit_var(l)] = Val::Unassigned;
        }
        if self.qhead > self.trail.len() {
            self.qhead = self.trail.len();
        }
    }

    /// Run unit propagation from current `qhead` until either
    /// fixpoint or conflict.  Returns `Err(())` on conflict, `Ok(())`
    /// on fixpoint.  Uses the standard watched-literal scheme.
    fn propagate(&mut self) -> Result<(), ()> {
        while self.qhead < self.trail.len() {
            let p = self.trail[self.qhead];
            self.qhead += 1;
            // Lits being assigned True invalidate clauses watching ¬p.
            let false_lit = lit_neg(p);
            // Iterate watchers of false_lit; rebuild list as we go
            // because watch maintenance reassigns watchers.
            let watchers = std::mem::take(&mut self.watches[false_lit]);
            let mut i = 0;
            while i < watchers.len() {
                let cid = watchers[i];
                if self.clauses[cid].deleted {
                    i += 1;
                    continue;
                }
                // Block-scope the &mut self.clauses borrow so that
                // self.enqueue / self.watches calls below can run
                // without conflict.
                let (need_unit, unit_lit, conflict): (bool, LitCode, bool) = {
                    let value = &self.value;
                    let clause = &mut self.clauses[cid];
                    // Ensure false_lit is at index 1 (canonical: other
                    // watch at index 0).
                    if clause.lits[0] == false_lit {
                        clause.lits.swap(0, 1);
                    }
                    // If the other watched lit is already True, the
                    // clause is satisfied — keep watching false_lit.
                    if !clause.lits.is_empty()
                        && Self::lit_val_in(value, clause.lits[0]) == Val::True
                    {
                        self.watches[false_lit].push(cid);
                        i += 1;
                        continue;
                    }
                    // Look for a replacement watch: any lit (other
                    // than index 0) that's not False.
                    let mut new_watch: Option<usize> = None;
                    for k in 2..clause.lits.len() {
                        if Self::lit_val_in(value, clause.lits[k]) != Val::False {
                            new_watch = Some(k);
                            break;
                        }
                    }
                    if let Some(k) = new_watch {
                        let new_lit = clause.lits[k];
                        clause.lits[1] = new_lit;
                        clause.lits[k] = false_lit;
                        self.watches[new_lit].push(cid);
                        i += 1;
                        continue;
                    }
                    // No replacement: clause is unit on lits[0] (if
                    // present), or trivially conflicting (empty
                    // clause).  Decide.
                    self.watches[false_lit].push(cid);
                    if clause.lits.is_empty() {
                        (false, 0, true)
                    } else {
                        match Self::lit_val_in(value, clause.lits[0]) {
                            Val::True       => (false, 0, false),
                            Val::False      => (false, 0, true),
                            Val::Unassigned => (true, clause.lits[0], false),
                        }
                    }
                };
                if conflict {
                    return Err(());
                }
                if need_unit {
                    if self.enqueue(unit_lit).is_err() {
                        return Err(());
                    }
                }
                i += 1;
            }
        }
        Ok(())
    }

    /// RUP-check: assume ¬l for each l in `clause` (pushed as
    /// units), propagate, expect conflict.  Restores trail on exit.
    /// `Ok(())` = RUP succeeded (clause is implied), `Err(())` =
    /// RUP failed (clause cannot be RUP-derived).
    fn rup_check(&mut self, clause: &[LitCode]) -> Result<(), ()> {
        let saved_trail = self.trail.len();
        let saved_qhead = self.qhead;
        // First propagate any pending units from prior steps.
        if self.propagate().is_err() {
            // Already UNSAT at this point — adding any clause is
            // trivially RUP.
            self.backtrack_to(saved_trail);
            self.qhead = saved_qhead;
            return Ok(());
        }
        // Empty clause: RUP succeeds iff the current set is already
        // UNSAT (no additional units to enqueue).  We already
        // propagated above; if no conflict came out, the empty
        // clause's RUP check fails.
        if clause.is_empty() {
            // Need explicit conflict via propagation alone.  Already
            // ran above without conflict → empty clause not RUP.
            // (But it's possible no further propagation is needed
            // and conflict requires checking some clause is empty.
            // The propagate() call above would've found that.)
            return Err(());
        }
        // Assume negation of each clause lit.
        for &l in clause {
            let neg = lit_neg(l);
            match self.lit_val(neg) {
                Val::True       => { /* already assumed-true; nothing to do */ }
                Val::False      => {
                    // Assuming neg conflicts with current trail —
                    // i.e., l is already True ⇒ clause is satisfied
                    // by current trail ⇒ trivially RUP.
                    self.backtrack_to(saved_trail);
                    self.qhead = saved_qhead;
                    return Ok(());
                }
                Val::Unassigned => {
                    if self.enqueue(neg).is_err() {
                        // Enqueue caused immediate conflict.
                        self.backtrack_to(saved_trail);
                        self.qhead = saved_qhead;
                        return Ok(());
                    }
                }
            }
        }
        let r = self.propagate();
        self.backtrack_to(saved_trail);
        self.qhead = saved_qhead;
        match r {
            Err(()) => Ok(()),   // conflict ⇒ RUP succeeded
            Ok(())  => Err(()),  // no conflict ⇒ RUP failed
        }
    }
}

// ─── Main ───────────────────────────────────────────────────────────────────

fn usage() -> ExitCode {
    eprintln!("usage: sat-drat-verify <cnf-file> <drat-file>");
    ExitCode::from(2)
}

fn main() -> ExitCode {
    let positional: Vec<String> = env::args().skip(1).collect();
    if positional.iter().any(|s| s == "-h" || s == "--help") { return usage(); }
    if positional.len() != 2 { return usage(); }
    let cnf_path: PathBuf = positional[0].clone().into();
    let drat_path: PathBuf = positional[1].clone().into();

    let cnf = match File::open(&cnf_path).map_err(|e| e.to_string())
        .and_then(|f| parse_dimacs(BufReader::new(f)))
    {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cnf parse failed ({}): {}", cnf_path.display(), e);
            return ExitCode::from(2);
        }
    };
    eprintln!("c F: vars={} clauses={}", cnf.nvars, cnf.clauses.len());

    let steps = match File::open(&drat_path).map_err(|e| e.to_string())
        .and_then(|f| parse_drat(BufReader::new(f)))
    {
        Ok(s) => s,
        Err(e) => {
            eprintln!("drat parse failed ({}): {}", drat_path.display(), e);
            return ExitCode::from(2);
        }
    };
    let n_add: usize = steps.iter().filter(|s| matches!(s, DratStep::Add(_))).count();
    let n_del: usize = steps.iter().filter(|s| matches!(s, DratStep::Delete(_))).count();
    let n_empty: usize = steps.iter().filter(|s| matches!(s, DratStep::Empty)).count();
    eprintln!("c proof: {} add, {} delete, {} empty (total {} steps)",
              n_add, n_del, n_empty, steps.len());

    // Initialize the checker with the original CNF.
    let mut checker = Checker::new(cnf.nvars);
    let mut already_unsat = false;
    for cls in &cnf.clauses {
        match checker.add_clause(cls.clone()) {
            Ok(_)  => {}
            Err(()) => { already_unsat = true; }
        }
    }
    if !already_unsat {
        // Run initial BCP to surface any direct conflict from the
        // CNF's unit clauses.
        if checker.propagate().is_err() {
            already_unsat = true;
        }
    }
    if already_unsat {
        eprintln!("c F is UNSAT before any proof step (trivial UNSAT)");
        let _ = writeln!(io::stdout(), "VALID UNSAT PROOF");
        return ExitCode::from(0);
    }

    // Replay each proof step.
    let start = std::time::Instant::now();
    let mut accepted_empty = false;
    for (i, step) in steps.iter().enumerate() {
        match step {
            DratStep::Add(c) => {
                if checker.rup_check(c).is_err() {
                    let lits: Vec<i32> = c.iter().map(|&l| lit_to_dimacs(l)).collect();
                    eprintln!("INVALID PROOF: step {} clause {:?} is not RUP-implied",
                              i + 1, lits);
                    let _ = writeln!(io::stdout(), "INVALID DRAT PROOF (step {} non-RUP)",
                                     i + 1);
                    return ExitCode::from(1);
                }
                if checker.add_clause(c.clone()).is_err() {
                    accepted_empty = true;
                    break;
                }
                // After adding, run propagation: the new clause may
                // make some lit unit that wasn't before.
                if checker.propagate().is_err() {
                    accepted_empty = true;
                    break;
                }
            }
            DratStep::Delete(c) => {
                checker.delete_clause(c);
            }
            DratStep::Empty => {
                // RUP check the empty clause: should reduce to "current
                // trail is already in conflict via propagation".
                if checker.rup_check(&[]).is_err() {
                    eprintln!("INVALID PROOF: empty clause at step {} not RUP-implied",
                              i + 1);
                    let _ = writeln!(io::stdout(), "INVALID DRAT PROOF (empty not RUP)");
                    return ExitCode::from(1);
                }
                accepted_empty = true;
                break;
            }
        }
    }
    let ms = start.elapsed().as_secs_f64() * 1000.0;
    if accepted_empty {
        eprintln!("c proof verified in {:.1}ms", ms);
        let _ = writeln!(io::stdout(), "VALID UNSAT PROOF");
        ExitCode::from(0)
    } else {
        eprintln!("INVALID PROOF: proof ended without deriving empty clause");
        let _ = writeln!(io::stdout(), "INVALID DRAT PROOF (no empty clause)");
        ExitCode::from(1)
    }
}
