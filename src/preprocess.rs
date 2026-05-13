//! Phase 1 NNF preprocessing: top-level unit propagation with witness
//! reconstruction.  See `doc/preprocess.md` for the full design.
//!
//! `preprocess(nnf)` repeatedly normalizes the NNF (flattens nested
//! same-kind nodes, drops identity children, propagates annihilators)
//! and forces any literal that appears as a top-level `Prod` child.
//! Iterates to fix-point.
//!
//! Returns the simplified NNF together with:
//!
//! - a `ReconstructionStack` for extending a path's literals into a
//!   full assignment over the original variables (SAT-witness side);
//! - a `PositionMap` for translating cover pairs in the simplified
//!   NNF back to positions in the original NNF (UNSAT-witness side);
//! - `lemma_covers`, a list of cover pairs derived directly by the
//!   preprocessor (e.g. when `a` and `a'` both appear as units in the
//!   same Prod).
//!
//! UP is SAT-direction: it forces literals true under the assumption
//! that the input NNF is to be *satisfied*.  Callers running a
//! satisfiability search on `F` should preprocess `F`; callers
//! running a validity search on `F` (= unsatisfiability of `¬F`)
//! should preprocess `F.complement()`.

use std::collections::HashMap;

use crate::matrix::{Cover, Lit, NNF, Pair, Position, Var};

/// Tagged NNF: every `Lit` leaf carries the position it occupied in
/// the *original* (pre-preprocessing) NNF.  All rewrites operate on
/// `NnfP` and preserve these tags; the final un-tag step recovers a
/// plain `NNF` plus a position-map.
#[derive(Clone, Debug)]
enum NnfP {
    Lit { lit: Lit, orig_pos: Position },
    Sum(Vec<NnfP>),
    Prod(Vec<NnfP>),
}

impl NnfP {
    fn from_nnf(nnf: &NNF) -> Self {
        fn walk(n: &NNF, pos: &mut Vec<usize>) -> NnfP {
            match n {
                NNF::Lit(l) => NnfP::Lit { lit: l.clone(), orig_pos: pos.clone() },
                NNF::Sum(ch) => NnfP::Sum(
                    ch.iter().enumerate().map(|(i, c)| {
                        pos.push(i);
                        let r = walk(c, pos);
                        pos.pop();
                        r
                    }).collect()
                ),
                NNF::Prod(ch) => NnfP::Prod(
                    ch.iter().enumerate().map(|(i, c)| {
                        pos.push(i);
                        let r = walk(c, pos);
                        pos.pop();
                        r
                    }).collect()
                ),
            }
        }
        walk(nnf, &mut vec![])
    }

    /// Strip tags, returning the plain `NNF` and a map from each
    /// surviving leaf's position in the new tree back to its position
    /// in the original tree.
    fn to_nnf_with_pos_map(&self) -> (NNF, HashMap<Position, Position>) {
        let mut map = HashMap::new();
        fn walk(
            n: &NnfP,
            cur: &mut Vec<usize>,
            map: &mut HashMap<Position, Position>,
        ) -> NNF {
            match n {
                NnfP::Lit { lit, orig_pos } => {
                    map.insert(cur.clone(), orig_pos.clone());
                    NNF::Lit(lit.clone())
                }
                NnfP::Sum(ch) => NNF::Sum(
                    ch.iter().enumerate().map(|(i, c)| {
                        cur.push(i);
                        let r = walk(c, cur, map);
                        cur.pop();
                        r
                    }).collect()
                ),
                NnfP::Prod(ch) => NNF::Prod(
                    ch.iter().enumerate().map(|(i, c)| {
                        cur.push(i);
                        let r = walk(c, cur, map);
                        cur.pop();
                        r
                    }).collect()
                ),
            }
        }
        let nnf = walk(self, &mut vec![], &mut map);
        (nnf, map)
    }
}

// ─── Position map ──────────────────────────────────────────────────────────

/// Forward map: leaf position in the *preprocessed* NNF →  leaf
/// position in the *original* NNF.  One-to-one in Phase 1 (no
/// transformation duplicates leaves).
#[derive(Debug, Default, Clone)]
pub struct PositionMap {
    forward: HashMap<Position, Position>,
}

impl PositionMap {
    pub fn translate(&self, pos: &Position) -> Option<Position> {
        self.forward.get(pos).cloned()
    }
    pub fn translate_pair(&self, pair: &Pair) -> Option<Pair> {
        Some((self.translate(&pair.0)?, self.translate(&pair.1)?))
    }
    /// Translate every pair; pairs whose endpoints don't translate are
    /// silently dropped (shouldn't happen in Phase 1 — every leaf
    /// surviving into the preprocessed NNF has a recorded original).
    pub fn translate_cover(&self, cover: &Cover) -> Cover {
        cover.iter().filter_map(|p| self.translate_pair(p)).collect()
    }
}

// ─── Reconstruction stack ──────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum ReconStep {
    /// `var := value` — forced unit literal (Phase 1, unit propagation).
    Unit { var: Var, value: bool },
    /// `var := defn.evaluate(surviving_asgn)` — variable was eliminated
    /// by a transformation that left an NNF expression as its
    /// definition.  Used by Phase 3 (at-most-K counter collapse: each
    /// counter aux `x_i,j` is defined as "at-least-j of d_1..d_i" =
    /// an NNF over the underlying d-variables) and by Phase 4 (BVE,
    /// when ready).  Replay evaluates the defn against the
    /// already-restored assignment.
    Defined { var: Var, defn: NNF },
}

#[derive(Debug, Default, Clone)]
pub struct ReconstructionStack {
    pub steps: Vec<ReconStep>,
}

impl ReconstructionStack {
    pub fn new() -> Self { Self { steps: Vec::new() } }

    pub fn push_unit(&mut self, var: Var, value: bool) {
        self.steps.push(ReconStep::Unit { var, value });
    }

    pub fn push_defined(&mut self, var: Var, defn: NNF) {
        self.steps.push(ReconStep::Defined { var, defn });
    }

    pub fn len(&self) -> usize { self.steps.len() }
    pub fn is_empty(&self) -> bool { self.steps.is_empty() }

    /// Extend a partial assignment over surviving variables with values
    /// for every variable eliminated during preprocessing.  Replayed
    /// in reverse insertion order so later `Defined` definitions can
    /// resolve against the already-restored assignment (the defn may
    /// reference earlier-pushed variables that were themselves
    /// eliminated; by the time we restore them in reverse order, they
    /// are present in `asgn`).
    ///
    /// **Precondition**: every *surviving* variable referenced by any
    /// `Defined` step's defn must already be in `asgn`.  Callers that
    /// don't know which variables survived should use
    /// [`Preprocessed::pad_survivors_and_extend`] instead, which
    /// handles padding before recon replay.
    pub fn extend_assignment(&self, asgn: &mut Vec<Lit>) {
        for step in self.steps.iter().rev() {
            match step {
                ReconStep::Unit { var, value } => {
                    if !asgn.iter().any(|l| l.var == *var) {
                        // `value == true` ⇒ positive lit (neg = false).
                        asgn.push(Lit { var: *var, neg: !*value });
                    }
                }
                ReconStep::Defined { var, defn } => {
                    if !asgn.iter().any(|l| l.var == *var) {
                        // Evaluate the defn against the surviving
                        // assignment + already-restored vars.  Any
                        // missing operand returns `Err(())`; we
                        // default that case to `false`, which is
                        // safe under the precondition above.
                        let value = defn.evaluate(asgn).unwrap_or(false);
                        asgn.push(Lit { var: *var, neg: !value });
                    }
                }
            }
        }
    }

    /// Return the set of variables eliminated by preprocessing (those
    /// that appear in *any* recon step).  Used to distinguish
    /// "surviving" variables (which need to be padded before recon
    /// replay) from "eliminated" variables (which the recon stack
    /// restores).
    pub fn eliminated_vars(&self) -> std::collections::HashSet<Var> {
        self.steps.iter().map(|s| match s {
            ReconStep::Unit    { var, .. } => *var,
            ReconStep::Defined { var, .. } => *var,
        }).collect()
    }

    /// Pad `asgn` with `var = false` for every surviving variable
    /// (those not eliminated and not already in `asgn`), *then* replay
    /// the recon stack.  The pre-pad-then-extend order is required by
    /// `Defined` recon steps (Phase 3 BVE), which evaluate their defns
    /// against survivor values: those must be in `asgn` already.
    pub fn pad_survivors_and_extend(&self, asgn: &mut Vec<Lit>, total_vars: u32) {
        let mut in_asgn: std::collections::HashSet<Var> =
            asgn.iter().map(|l| l.var).collect();
        let eliminated = self.eliminated_vars();
        for var in 0..total_vars {
            if !in_asgn.contains(&var) && !eliminated.contains(&var) {
                asgn.push(Lit { var, neg: true }); // default: var = false
                in_asgn.insert(var);
            }
        }
        self.extend_assignment(asgn);
    }
}

// ─── Preprocessed result ───────────────────────────────────────────────────

#[derive(Debug, Clone)]
pub struct Preprocessed {
    pub nnf: NNF,
    pub recon: ReconstructionStack,
    pub pos_map: PositionMap,
    /// Cover pairs derived directly by the preprocessor (e.g. when a
    /// `Prod` has both `Lit(a)` and `Lit(a')` as direct children).
    /// Their positions are in the original NNF — translation through
    /// `pos_map` is *not* needed.
    pub lemma_covers: Cover,
}

impl Preprocessed {
    /// Translate the literals on a non-complementary path through
    /// `pp.nnf.complement()` into a partial satisfying assignment
    /// over the *original* variables of the input NNF.
    ///
    /// The path's literals come from the complement; the assignment
    /// we want is in the F-direction, so each path literal is
    /// negated.  The reconstruction stack (already F-direction) is
    /// then replayed to recover any variables eliminated during
    /// preprocessing.  Variables touched by neither side are absent
    /// — the caller may fill them with don't-cares.
    pub fn reconstruct_sat_assignment(&self, comp_path_lits: Vec<Lit>) -> Vec<Lit> {
        let mut asgn: Vec<Lit> = comp_path_lits.into_iter()
            .map(|l| l.complement())
            .collect();
        self.recon.extend_assignment(&mut asgn);
        asgn
    }

    /// Translate the literals on a non-complementary path through
    /// `pp.nnf` (validity-direction) into a partial falsifying
    /// assignment over the original variables.  Same shape as
    /// `reconstruct_sat_assignment` but for the dual direction:
    /// here the path is on the formula itself (we're enumerating
    /// witnesses of non-tautology), so we negate to get a falsifier.
    pub fn reconstruct_falsifying_assignment(&self, path_lits: Vec<Lit>) -> Vec<Lit> {
        let mut asgn: Vec<Lit> = path_lits.into_iter()
            .map(|l| l.complement())
            .collect();
        self.recon.extend_assignment(&mut asgn);
        asgn
    }

    /// Translate a cover (in preprocessed-NNF positions) back to
    /// original-NNF positions and prepend any lemma covers derived
    /// during preprocessing.  Positions are stable across NNF
    /// complement (structure is identical, only polarities flip), so
    /// the same `pos_map` translates both validity-direction covers
    /// (on `pp.nnf`) and satisfiability-direction covers (on
    /// `pp.nnf.complement()`).
    pub fn reconstruct_cover(&self, cover: &Cover) -> Cover {
        let mut out = self.lemma_covers.clone();
        out.extend(self.pos_map.translate_cover(cover));
        out
    }

    /// Convenience wrapper around
    /// [`ReconstructionStack::pad_survivors_and_extend`].
    pub fn pad_survivors_and_extend(&self, asgn: &mut Vec<Lit>, total_vars: u32) {
        self.recon.pad_survivors_and_extend(asgn, total_vars);
    }
}

// ─── Driver ────────────────────────────────────────────────────────────────

/// Run preprocessing passes to fix-point: Phase 1 (top-level unit
/// propagation) alternating with Phase 3 (bounded-occurrence BVE,
/// targeting at-most-K sequential-counter aux variables).  Each BVE
/// elimination can produce new resolvents that surface as unit
/// clauses, so we loop UP and BVE until neither makes progress.
pub fn preprocess(nnf: &NNF) -> Preprocessed {
    let mut tagged = NnfP::from_nnf(nnf);
    let mut recon = ReconstructionStack::new();
    let mut lemma_covers: Cover = Vec::new();

    loop {
        let up_did = up_to_fixpoint(&mut tagged, &mut recon, &mut lemma_covers);
        // After UP collapses every forced unit, do one round of BVE
        // (which may eliminate aux counter variables and surface new
        // units in their resolvents).  Then loop back for another UP
        // round.
        let bve_did = bve_to_fixpoint(&mut tagged, &mut recon);
        if !up_did && !bve_did { break; }
    }

    let (nnf, fwd) = tagged.to_nnf_with_pos_map();
    Preprocessed {
        nnf,
        recon,
        pos_map: PositionMap { forward: fwd },
        lemma_covers,
    }
}

/// Top-level unit-propagation loop.  Returns `true` if any rewrite
/// happened (so the driver knows to loop back to BVE).
fn up_to_fixpoint(
    tagged: &mut NnfP,
    recon: &mut ReconstructionStack,
    lemma_covers: &mut Cover,
) -> bool {
    let mut any_change = false;
    loop {
        normalize(tagged);
        match collect_top_units(tagged) {
            UnitScan::None => return any_change,
            UnitScan::Contradiction(pair) => {
                lemma_covers.push(pair);
                *tagged = NnfP::Sum(vec![]); // false
                return true;
            }
            UnitScan::Units { values, positions } => {
                for (var, value) in values.iter() {
                    recon.push_unit(*var, *value);
                }
                substitute_units(tagged, &values, &positions, lemma_covers);
                any_change = true;
            }
        }
    }
}

// ─── Unit scan ─────────────────────────────────────────────────────────────

enum UnitScan {
    /// No top-level unit literals found.
    None,
    /// At least one unit literal found; no contradiction.
    Units {
        values:    HashMap<Var, bool>,
        positions: HashMap<Var, Position>,
    },
    /// Two complementary top-level units found.  The pair holds the
    /// original positions of `var` and `var'` for the lemma cover.
    Contradiction(Pair),
}

fn collect_top_units(n: &NnfP) -> UnitScan {
    let lits: Vec<(&Lit, &Position)> = match n {
        NnfP::Lit { lit, orig_pos } => vec![(lit, orig_pos)],
        NnfP::Prod(ch) => ch.iter().filter_map(|c| {
            if let NnfP::Lit { lit, orig_pos } = c { Some((lit, orig_pos)) } else { None }
        }).collect(),
        NnfP::Sum(_) => vec![],
    };

    if lits.is_empty() { return UnitScan::None; }

    let mut values: HashMap<Var, bool> = HashMap::new();
    let mut positions: HashMap<Var, Position> = HashMap::new();
    for (lit, orig_pos) in lits {
        let value = !lit.neg; // positive lit ⇒ var = true
        match values.get(&lit.var).copied() {
            Some(prev) if prev != value => {
                return UnitScan::Contradiction((
                    positions[&lit.var].clone(),
                    orig_pos.clone(),
                ));
            }
            _ => {
                values.insert(lit.var, value);
                positions.insert(lit.var, orig_pos.clone());
            }
        }
    }
    UnitScan::Units { values, positions }
}

// ─── Substitution ──────────────────────────────────────────────────────────

/// Apply each forced unit value to every literal in the tree.  When a
/// literal evaluates to FALSE under its variable's unit value, that
/// position together with the unit's position forms a complementary
/// pair — emit it as a lemma cover.  These lemmas certify the
/// substitution: any path through the original NNF that visits both
/// positions has the literals (l, ¬l) and is therefore covered.
fn substitute_units(
    n: &mut NnfP,
    values: &HashMap<Var, bool>,
    positions: &HashMap<Var, Position>,
    lemma_covers: &mut Cover,
) {
    match n {
        NnfP::Lit { lit, orig_pos } => {
            if let Some(&value) = values.get(&lit.var) {
                let lit_true = (!lit.neg) == value;
                if lit_true {
                    *n = NnfP::Prod(vec![]); // true
                } else {
                    // Lit at orig_pos evaluates to FALSE under the unit
                    // value.  The unit position (where the forcing lit
                    // lives) and orig_pos hold complementary literals.
                    let unit_pos = positions[&lit.var].clone();
                    // Don't emit the trivial self-cover (unit_pos == orig_pos
                    // can only happen if a literal is its own complement,
                    // which is impossible — but guard anyway).
                    if unit_pos != *orig_pos {
                        lemma_covers.push((unit_pos, orig_pos.clone()));
                    }
                    *n = NnfP::Sum(vec![]); // false
                }
            }
        }
        NnfP::Sum(ch) | NnfP::Prod(ch) => {
            for c in ch.iter_mut() {
                substitute_units(c, values, positions, lemma_covers);
            }
        }
    }
}

// ─── Normalize ─────────────────────────────────────────────────────────────

/// Recursive normalization that:
/// - flattens same-kind nested children (`Sum` inside `Sum`, `Prod`
///   inside `Prod`),
/// - drops identity children (`Sum([])` = false from a `Sum`,
///   `Prod([])` = true from a `Prod`),
/// - propagates annihilators (`Prod([])` = true in a `Sum`, `Sum([])`
///   = false in a `Prod`),
/// - collapses singletons (`Sum([x])` → `x`, `Prod([x])` → `x`).
fn normalize(n: &mut NnfP) {
    let is_sum;
    let owned;
    match n {
        NnfP::Lit { .. } => return,
        NnfP::Sum(ch) => {
            is_sum = true;
            for c in ch.iter_mut() { normalize(c); }
            owned = std::mem::take(ch);
        }
        NnfP::Prod(ch) => {
            is_sum = false;
            for c in ch.iter_mut() { normalize(c); }
            owned = std::mem::take(ch);
        }
    }

    let mut flat: Vec<NnfP> = Vec::with_capacity(owned.len());
    let mut annihilated = false;
    for c in owned.into_iter() {
        let is_true_const = matches!(&c, NnfP::Prod(inner) if inner.is_empty());
        let is_false_const = matches!(&c, NnfP::Sum(inner) if inner.is_empty());
        if is_sum {
            if is_true_const { annihilated = true; break; }
            if is_false_const { continue; }
            // Flatten Sum-in-Sum
            if let NnfP::Sum(inner) = c {
                flat.extend(inner);
            } else {
                flat.push(c);
            }
        } else {
            if is_false_const { annihilated = true; break; }
            if is_true_const { continue; }
            // Flatten Prod-in-Prod
            if let NnfP::Prod(inner) = c {
                flat.extend(inner);
            } else {
                flat.push(c);
            }
        }
    }

    *n = if annihilated {
        if is_sum { NnfP::Prod(vec![]) } else { NnfP::Sum(vec![]) }
    } else if flat.is_empty() {
        if is_sum { NnfP::Sum(vec![]) } else { NnfP::Prod(vec![]) }
    } else if flat.len() == 1 {
        flat.into_iter().next().unwrap()
    } else if is_sum {
        NnfP::Sum(flat)
    } else {
        NnfP::Prod(flat)
    };
}

// ─── Phase 3: bounded-occurrence variable elimination (BVE) ────────────────
//
// Targets the sequential-counter aux variables used in canonical
// at-most-K encodings.  Each aux `x_i,j` appears ≤2 times positively
// and ≤2 times negatively across the top-level Prod clauses, so it
// resolves out without size blow-up.  Resolution naturally inlines
// already-eliminated aux variables (their replaced clauses now
// mention surviving variables), so the reconstruction defn for each
// aux references only surviving variables.

/// BVE candidate bound: max positive and max negative occurrences
/// considered for elimination.  Loosened to (8, 8) for Phase 4
/// (broader Tseitin aux elimination): typical gate-encoding aux
/// vars have ≤8 occurrences per polarity (carry-chain aux vars in
/// BMC use multiple gates per stage, so an aux can have 4-6
/// definition occurrences plus 2-4 use occurrences).  The size
/// guard inside `apply_bve` still rejects any elimination that
/// grows total lit count — most gate definitions produce
/// tautological resolvents that drop, keeping the formula smaller.
const BVE_MAX_POS: usize = 8;
const BVE_MAX_NEG: usize = 8;

/// Run BVE to fix-point.  Returns `true` if any variable was
/// eliminated.
fn bve_to_fixpoint(tagged: &mut NnfP, recon: &mut ReconstructionStack) -> bool {
    let mut any_change = false;
    while bve_one_step(tagged, recon) {
        any_change = true;
    }
    any_change
}

/// Eliminate at most one variable.  Returns `true` if a variable was
/// eliminated.  Only operates on CNF-shaped NNFs (top-level Prod of
/// clauses; each clause is a single `Lit` or `Sum` of `Lit`s).
///
/// Iterates eligible candidates from smallest `p × n` upward — if a
/// candidate's `apply_bve` rejects on the size guard, try the next
/// one.  Returns `true` as soon as any candidate succeeds; `false`
/// when no candidate passes.
fn bve_one_step(tagged: &mut NnfP, recon: &mut ReconstructionStack) -> bool {
    let NnfP::Prod(_) = tagged else { return false; };

    let candidates: Vec<Var> = {
        let children = match tagged {
            NnfP::Prod(ch) => ch,
            _ => return false,
        };
        // For each variable, (positive occurrence count, negative
        // occurrence count, all-occurrences-in-clauses flag).
        let mut occ: HashMap<Var, (usize, usize, bool)> = HashMap::new();
        for c in children.iter() {
            match extract_clause_lits(c) {
                Some(lits) => {
                    for lit in &lits {
                        let entry = occ.entry(lit.var).or_insert((0, 0, true));
                        if lit.neg { entry.1 += 1; } else { entry.0 += 1; }
                    }
                }
                None => {
                    let mut vars = Vec::new();
                    collect_vars(c, &mut vars);
                    for v in vars {
                        let entry = occ.entry(v).or_insert((0, 0, true));
                        entry.2 = false;
                    }
                }
            }
        }
        let mut cands: Vec<(Var, usize)> = occ.iter()
            .filter(|&(_, &(_, _, ok))| ok)
            .filter(|&(_, &(p, n, _))| p > 0 && n > 0
                                    && p <= BVE_MAX_POS && n <= BVE_MAX_NEG)
            .map(|(&v, &(p, n, _))| (v, p * n))
            .collect();
        // Sort by (cost, var) so tie-breaks are deterministic.  Using
        // raw `sort_by_key(cost)` plus the `occ` HashMap's
        // non-deterministic iteration order otherwise produces
        // different BVE-elimination sequences across runs of the same
        // formula → different simplified-NNF clause orderings → wide
        // variance in downstream search times.
        cands.sort_by_key(|&(v, cost)| (cost, v));
        cands.into_iter().map(|(v, _)| v).collect()
    };

    for var in candidates {
        if apply_bve(tagged, var, recon) {
            return true;
        }
    }
    false
}

/// Attempt to eliminate `var` by resolution.  Returns `true` if BVE
/// applied, `false` if rejected by the size guard (the formula's
/// total literal count would grow).  Size growth on every BVE
/// produces compounding overhead in the matrix-method search even
/// when individual steps look free — we observed regressions on
/// at-most-2 (a single mid-chain aux BVE grows the lit count from 9
/// to 10, but compounded over a 16-stage chain on faulty-adder this
/// pushed `matrix.smart`/`matrix.cdcl` from 60ms to TIMEOUT).
fn apply_bve(tagged: &mut NnfP, var: Var, recon: &mut ReconstructionStack) -> bool {
    let children = match tagged {
        NnfP::Prod(ch) => ch,
        _ => return false,
    };
    let owned = std::mem::take(children);

    let mut pos_clauses: Vec<NnfP> = Vec::new();
    let mut neg_clauses: Vec<NnfP> = Vec::new();
    let mut other: Vec<NnfP> = Vec::new();
    for c in owned {
        let Some(lits) = extract_clause_lits(&c) else {
            other.push(c);
            continue;
        };
        let has_pos = lits.iter().any(|l| l.var == var && !l.neg);
        let has_neg = lits.iter().any(|l| l.var == var && l.neg);
        match (has_pos, has_neg) {
            (true, true)   => { /* tautological w.r.t. `var`; drop */ }
            (true, false)  => pos_clauses.push(c),
            (false, true)  => neg_clauses.push(c),
            (false, false) => other.push(c),
        }
    }

    // Compute resolvents first so we can check the size guard.
    let mut resolvents: Vec<NnfP> = Vec::new();
    for p in &pos_clauses {
        for n in &neg_clauses {
            if let Some(r) = resolve_clauses(p, n, var) {
                resolvents.push(r);
            }
        }
    }

    // Size guard: only apply BVE if it doesn't grow the formula's
    // total literal count (counting only the clauses we're about to
    // remove vs. the resolvents we're about to add — `other` is
    // untouched).  Tried relaxing to `new ≤ orig × 1.25` for Phase 4
    // hoping to capture BMC's count-zeros gate aux vars: it produced
    // *more* BVE eliminations (164 vs 88 on faulty_add 16/2 SAT) but
    // *fewer* leaf reductions, suggesting BVE was chasing
    // marginal-gain auxes that net-grow the matrix.  Strict
    // no-growth is the sweet spot.
    let orig_lits: usize = pos_clauses.iter().chain(neg_clauses.iter())
        .map(|c| extract_clause_lits(c).map(|l| l.len()).unwrap_or(0))
        .sum();
    let new_lits: usize = resolvents.iter()
        .map(|c| extract_clause_lits(c).map(|l| l.len()).unwrap_or(0))
        .sum();
    if new_lits > orig_lits {
        // Restore: put the original clauses back, drop the
        // resolvents.  Defn is not pushed.
        let mut restored = pos_clauses;
        restored.extend(neg_clauses);
        restored.extend(other);
        *children = restored;
        return false;
    }

    // Record the reconstruction defn before consuming pos_clauses.
    // The clauses removed at this BVE step mention ONLY surviving
    // variables (plus `var`) — because prior BVE rounds already
    // inlined any earlier-eliminated variables via resolution — so
    // the defn references survivors only.
    let defn = build_bve_defn(&pos_clauses, var);
    recon.push_defined(var, defn);

    let mut new_children = other;
    new_children.extend(resolvents);
    *children = new_children;
    true
}

/// For each positive clause `(other_lits ∨ var)`, the clause forces
/// `var = true` exactly when all `other_lits` are false.  The
/// reconstruction defn for `var` is therefore:
///
/// ```text
/// var ⇔ OR over positive_clauses of (AND of ¬other_lits)
/// ```
fn build_bve_defn(pos_clauses: &[NnfP], var: Var) -> NNF {
    let disjuncts: Vec<NNF> = pos_clauses.iter().filter_map(|c| {
        let lits = extract_clause_lits(c)?;
        let other_neg: Vec<NNF> = lits.iter()
            .filter(|l| l.var != var)
            .map(|l| NNF::Lit(l.complement()))
            .collect();
        Some(if other_neg.is_empty() {
            NNF::Prod(vec![]) // empty AND = TRUE (this is a unit clause `var`)
        } else if other_neg.len() == 1 {
            other_neg.into_iter().next().unwrap()
        } else {
            NNF::Prod(other_neg)
        })
    }).collect();
    if disjuncts.is_empty() {
        NNF::Sum(vec![]) // FALSE — no positive clause, var can default false
    } else if disjuncts.len() == 1 {
        disjuncts.into_iter().next().unwrap()
    } else {
        NNF::Sum(disjuncts)
    }
}

/// Resolve two clauses on `var`.  Returns the resolvent (with `var`
/// removed), or `None` if the result is a tautology (contains some
/// other variable both positively and negatively).
fn resolve_clauses(p: &NnfP, n: &NnfP, var: Var) -> Option<NnfP> {
    let p_lits = extract_clause_lits_with_pos(p);
    let n_lits = extract_clause_lits_with_pos(n);
    let mut out: Vec<NnfP> = Vec::new();
    let mut seen: HashMap<Var, bool> = HashMap::new();
    for (lit, orig_pos) in p_lits.into_iter().chain(n_lits.into_iter()) {
        if lit.var == var { continue; }
        if let Some(&prev_neg) = seen.get(&lit.var) {
            if prev_neg != lit.neg { return None; } // tautology
            // duplicate of same polarity: skip
        } else {
            seen.insert(lit.var, lit.neg);
            out.push(NnfP::Lit { lit, orig_pos });
        }
    }
    Some(match out.len() {
        0 => NnfP::Sum(vec![]), // empty clause = FALSE (unsat signal)
        1 => out.into_iter().next().unwrap(),
        _ => NnfP::Sum(out),
    })
}

/// Extract the literals from a clause-shaped `NnfP` — either a single
/// `Lit` (a unit clause) or a `Sum` whose every child is a `Lit`.
/// Returns `None` if the node isn't clause-shaped (so the caller knows
/// the contained variables aren't BVE-eligible).
fn extract_clause_lits(c: &NnfP) -> Option<Vec<Lit>> {
    match c {
        NnfP::Lit { lit, .. } => Some(vec![lit.clone()]),
        NnfP::Sum(children) => {
            let mut out = Vec::with_capacity(children.len());
            for s in children {
                match s {
                    NnfP::Lit { lit, .. } => out.push(lit.clone()),
                    _ => return None,
                }
            }
            Some(out)
        }
        _ => None,
    }
}

fn extract_clause_lits_with_pos(c: &NnfP) -> Vec<(Lit, Position)> {
    match c {
        NnfP::Lit { lit, orig_pos } => vec![(lit.clone(), orig_pos.clone())],
        NnfP::Sum(children) => children.iter().filter_map(|s| match s {
            NnfP::Lit { lit, orig_pos } => Some((lit.clone(), orig_pos.clone())),
            _ => None,
        }).collect(),
        _ => Vec::new(),
    }
}

fn collect_vars(n: &NnfP, out: &mut Vec<Var>) {
    match n {
        NnfP::Lit { lit, .. } => out.push(lit.var),
        NnfP::Sum(ch) | NnfP::Prod(ch) => {
            for c in ch { collect_vars(c, out); }
        }
    }
}

// ─── Tests ─────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::controller::PathSearchController;
    use crate::matrix::{Matrix, PathParams, PathsClass};

    /// Helper: evaluate an NNF under a full assignment (every variable
    /// mentioned in the formula assigned a polarity).  Returns the
    /// boolean value, panicking on under-determination.
    fn eval(nnf: &NNF, asgn: &[Lit]) -> bool {
        match nnf.evaluate(asgn) {
            Ok(b) => b,
            Err(()) => panic!("assignment {:?} is incomplete for NNF", asgn),
        }
    }

    /// Helper: given the literals of a non-complementary path through
    /// `preprocessed.nnf.complement()`, reconstruct a full assignment
    /// (padding survivors before replaying recon, then verifying) and
    /// confirm it satisfies the *original* NNF.
    fn check_sat_witness(original: &NNF, comp_path_lits: Vec<Lit>, pp: &Preprocessed, num_vars: u32) {
        // Convert comp-path lits to F-direction (negate), then use the
        // pad-and-extend helper so that survivors are pinned BEFORE
        // any Defined recon step evaluates its defn against them.
        let mut full: Vec<Lit> = comp_path_lits.into_iter().map(|l| l.complement()).collect();
        pp.pad_survivors_and_extend(&mut full, num_vars);
        assert!(eval(original, &full),
                "reconstructed assignment {:?} does not satisfy original NNF", full);
    }

    fn n_vars(m: &Matrix) -> u32 { m.ast.vars.len() as u32 }

    #[test]
    fn unit_at_root_fires() {
        // F = a → preprocess forces a=true, simplified = true (Prod([])).
        let m = Matrix::try_from("a").unwrap();
        let pp = preprocess(&m.nnf);
        assert_eq!(pp.recon.len(), 1);
        // Simplified NNF is Prod([]) = true.
        assert!(matches!(pp.nnf, NNF::Prod(ref ch) if ch.is_empty()));
        // Witness: just a=true from recon.
        check_sat_witness(&m.nnf, vec![], &pp, n_vars(&m));
    }

    #[test]
    fn chain_of_units_cascades() {
        // F = a · (a' + b) — UP forces a=true, then Sum([F, b]) → b → forces b=true.
        let m = Matrix::try_from("a (a' + b)").unwrap();
        let pp = preprocess(&m.nnf);
        assert_eq!(pp.recon.len(), 2);
        assert!(matches!(pp.nnf, NNF::Prod(ref ch) if ch.is_empty()));
        check_sat_witness(&m.nnf, vec![], &pp, n_vars(&m));
    }

    #[test]
    fn contradiction_yields_lemma_cover() {
        // F = a · a' — UP detects contradictory units.
        let m = Matrix::try_from("a a'").unwrap();
        let pp = preprocess(&m.nnf);
        // Simplified to Sum([]) = false.
        assert!(matches!(pp.nnf, NNF::Sum(ref ch) if ch.is_empty()));
        // One lemma cover, complementary, both endpoints in the original NNF.
        assert_eq!(pp.lemma_covers.len(), 1);
        let (pa, pb) = &pp.lemma_covers[0];
        let la = m.nnf.lit_at(pa).expect("pa resolves");
        let lb = m.nnf.lit_at(pb).expect("pb resolves");
        assert!(la.is_complement_of(lb));
    }

    #[test]
    fn partial_simplification_preserves_survivors() {
        // F = a · (b + c) — a forced, (b + c) survives.
        let m = Matrix::try_from("a (b + c)").unwrap();
        let pp = preprocess(&m.nnf);
        assert_eq!(pp.recon.len(), 1);
        // Simplified NNF is the Sum([b, c]) (after Prod-singleton collapse).
        match &pp.nnf {
            NNF::Sum(ch) => assert_eq!(ch.len(), 2),
            other => panic!("expected Sum([b, c]), got {:?}", other),
        }
        // Pos-map: the surviving b and c map to their original positions [1, 0] and [1, 1].
        let pos_b_new = vec![0usize];
        let pos_c_new = vec![1usize];
        assert_eq!(pp.pos_map.translate(&pos_b_new), Some(vec![1, 0]));
        assert_eq!(pp.pos_map.translate(&pos_c_new), Some(vec![1, 1]));
        // SAT witness: pp.nnf.complement() is Prod([Lit b', Lit c']); pick path [0]
        // (Lit b' chosen).  check_sat_witness negates → {b=true}.  With recon
        // {a=true} and padding c=false: {a, b, c'} satisfies F.
        let b = m.ast.var_index["b"];
        check_sat_witness(&m.nnf, vec![Lit { var: b, neg: true }], &pp, n_vars(&m));
    }

    #[test]
    fn dnf_root_no_units() {
        // F = a + b — Sum-rooted, no top-level units → preprocess is a no-op.
        let m = Matrix::try_from("a + b").unwrap();
        let pp = preprocess(&m.nnf);
        assert!(pp.recon.is_empty());
        assert!(pp.lemma_covers.is_empty());
        // Pos-map is the identity over the two leaves.
        assert_eq!(pp.pos_map.translate(&vec![0]), Some(vec![0]));
        assert_eq!(pp.pos_map.translate(&vec![1]), Some(vec![1]));
    }

    /// Run the matrix-method SAT check on the preprocessed NNF and
    /// verify that reconstructed witnesses are correct.
    fn sat_roundtrip(formula: &str, expected_sat: bool) {
        let m = Matrix::try_from(formula).unwrap();
        let pp = preprocess(&m.nnf);
        let nv = n_vars(&m);

        // Run the matrix-method SAT check on the *preprocessed* NNF.
        // I.e., enumerate paths of the complement and look for an uncovered one.
        let comp = pp.nnf.complement();
        let mut classes = Vec::new();
        {
            let mut ctrl = crate::matrix::BacktrackWhenCoveredController::with_on_class(
                Some(PathParams {
                    paths_class_limit: usize::MAX,
                    uncovered_path_limit: usize::MAX,
                    covered_prefix_limit: usize::MAX,
                    no_cover: false,
                }),
                |c, _| { classes.push(c); true },
            );
            comp.paths(&mut ctrl);
        }

        let result = crate::matrix::Paths { classes, hit_limit: false };
        let uncov = result.uncovered_paths().next().cloned();
        let cover = result.cover();

        match (expected_sat, uncov) {
            (true, Some(path)) => {
                // SAT — reconstruct the witness.
                let lits = comp.lits_on_path(&path).iter().map(|&l| l.clone()).collect();
                check_sat_witness(&m.nnf, lits, &pp, nv);
            }
            (true, None) => panic!(
                "{}: expected SAT but preprocessed-comp had no uncovered path", formula
            ),
            (false, None) => {
                // UNSAT — translate cover; verify it covers every path through
                // the *original complement* (which is what the SAT search
                // would have been certifying valid).
                let translated = pp.reconstruct_cover(&cover);
                let original_comp = m.nnf.complement();
                for path in original_comp.paths_iter() {
                    let positions = original_comp.positions_on_path(&path);
                    let covered = translated.iter().any(|(pa, pb)|
                        positions.contains(pa) && positions.contains(pb));
                    assert!(covered,
                        "cover {:?} (translated from {:?}) misses comp path {:?} of {}",
                        translated, cover, path, formula);
                }
            }
            (false, Some(path)) => panic!(
                "{}: expected UNSAT but preprocessed-comp had uncovered path {:?}",
                formula, path,
            ),
        }
    }

    #[test] fn roundtrip_sat_single_var() { sat_roundtrip("a", true); }
    #[test] fn roundtrip_sat_units_cascade() { sat_roundtrip("a (a' + b)", true); }
    #[test] fn roundtrip_sat_simple_or() { sat_roundtrip("a + b", true); }
    #[test] fn roundtrip_unsat_contradiction() { sat_roundtrip("a a'", false); }
    #[test] fn roundtrip_unsat_chain() { sat_roundtrip("a (a' + b) b'", false); }
    #[test] fn roundtrip_sat_pigeonhole_small() {
        // (a + b)(a' + c)(b' + c') — SAT (e.g. a=true, b=false, c=true).
        sat_roundtrip("(a + b)(a' + c)(b' + c')", true);
    }
    #[test] fn roundtrip_unsat_three_clauses() {
        // (a)(b)(a' + b') — UNSAT (a=b=true required, but a'+b' both false).
        sat_roundtrip("a b (a' + b')", false);
    }

    /// Fuzz: random small CNF formulas, preprocess, verify witness.
    #[test]
    fn fuzz_round_trip_small_cnf() {
        fn lcg(s: &mut u64) -> u64 {
            *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            *s
        }
        let mut s = 0xC0FFEEu64;
        for _trial in 0..40 {
            let n_vars = (lcg(&mut s) as usize % 5) + 2;
            let n_clauses = (lcg(&mut s) as usize % 6) + 1;
            let mut clauses: Vec<String> = Vec::new();
            for _ in 0..n_clauses {
                let len = (lcg(&mut s) as usize % 3) + 1;
                let mut lits: Vec<String> = Vec::new();
                for _ in 0..len {
                    let v = (lcg(&mut s) as usize % n_vars) as u8 + b'a';
                    let neg = lcg(&mut s) & 1 == 0;
                    let lit = format!("{}{}", v as char, if neg { "'" } else { "" });
                    if !lits.contains(&lit) { lits.push(lit); }
                }
                clauses.push(format!("({})", lits.join(" + ")));
            }
            let formula = clauses.join(" ");
            let m = match Matrix::try_from(formula.as_str()) {
                Ok(m) => m, Err(_) => continue,
            };
            let pp = preprocess(&m.nnf);
            let nv = n_vars as u32;

            // Run reference SAT check via the original (un-preprocessed) NNF.
            let mut original_sat = false;
            for path in m.nnf.complement().paths_iter() {
                if !m.nnf.complement().is_complementary(&path) { original_sat = true; break; }
            }

            // Run SAT check via the preprocessed NNF and reconstruct.
            let comp = pp.nnf.complement();
            let mut classes: Vec<PathsClass> = Vec::new();
            {
                let mut ctrl = crate::matrix::BacktrackWhenCoveredController::with_on_class(
                    Some(PathParams {
                        paths_class_limit: usize::MAX,
                        uncovered_path_limit: 1,
                        covered_prefix_limit: usize::MAX,
                        no_cover: false,
                    }),
                    |c, _| { classes.push(c); true },
                );
                comp.paths(&mut ctrl);
            }
            let result = crate::matrix::Paths { classes, hit_limit: false };
            let pp_sat = result.uncovered_paths().next().is_some();

            assert_eq!(pp_sat, original_sat,
                "formula {:?}: preprocessor changed SAT verdict ({} → {})",
                formula, original_sat, pp_sat);

            if pp_sat {
                let path = result.uncovered_paths().next().unwrap().clone();
                let lits: Vec<Lit> = comp.lits_on_path(&path).iter().map(|&l| l.clone()).collect();
                check_sat_witness(&m.nnf, lits, &pp, nv);
            } else {
                let cover = result.cover();
                let translated = pp.reconstruct_cover(&cover);
                let original_comp = m.nnf.complement();
                for path in original_comp.paths_iter() {
                    let positions = original_comp.positions_on_path(&path);
                    let covered = translated.iter().any(|(pa, pb)|
                        positions.contains(pa) && positions.contains(pb));
                    assert!(covered,
                        "formula {:?}: cover {:?} (translated from {:?}) misses comp path {:?}",
                        formula, translated, cover, path);
                }
            }
        }
    }

    // ─── Tests for Matrix::preprocess_for_search ──────────────────────────

    /// Drive a SAT-direction search through `preprocess_for_search`
    /// and verify: (a) the search-target NNF gives the same yes/no
    /// answer as searching `matrix.nnf_complement` directly, and (b)
    /// path-positions and cover-pair-positions emitted by the search
    /// translate (via `pp.pos_map`) to positions that correctly
    /// reference leaves of the original `matrix.nnf_complement`.
    fn preprocess_for_search_roundtrip(formula: &str, expected_sat: bool) {
        let m = Matrix::try_from(formula).unwrap();
        let (search_target, pp) = m.preprocess_for_search(true);

        // Reference: run the un-preprocessed SAT search on
        // `m.nnf_complement` and record what it found.
        let mut ref_uncov = None;
        {
            let mut ctrl = crate::matrix::BacktrackWhenCoveredController::with_on_class(
                Some(PathParams {
                    paths_class_limit: usize::MAX,
                    uncovered_path_limit: 1,
                    covered_prefix_limit: usize::MAX,
                    no_cover: false,
                }),
                |c, _| {
                    if let PathsClass::Uncovered(p) = c {
                        if ref_uncov.is_none() { ref_uncov = Some(p); }
                        false
                    } else { true }
                },
            );
            m.nnf_complement.paths(&mut ctrl);
        }
        let ref_sat = ref_uncov.is_some();
        assert_eq!(ref_sat, expected_sat,
            "{}: reference SAT verdict mismatch", formula);

        // Run the search on the *preprocessed* search target.
        let mut pp_uncov: Option<crate::matrix::ProdPath> = None;
        let mut pp_classes: Vec<PathsClass> = Vec::new();
        {
            let mut ctrl = crate::matrix::BacktrackWhenCoveredController::with_on_class(
                Some(PathParams {
                    paths_class_limit: usize::MAX,
                    uncovered_path_limit: 1,
                    covered_prefix_limit: usize::MAX,
                    no_cover: false,
                }),
                |c, _| { pp_classes.push(c); true },
            );
            search_target.paths(&mut ctrl);
        }
        for c in &pp_classes {
            if let PathsClass::Uncovered(p) = c {
                if pp_uncov.is_none() { pp_uncov = Some(p.clone()); }
            }
        }
        let pp_sat = pp_uncov.is_some();
        assert_eq!(pp_sat, expected_sat,
            "{}: preprocessed SAT verdict mismatch", formula);

        if pp_sat {
            // Reconstruct a satisfying assignment from the path's literals.
            let path = pp_uncov.unwrap();
            let path_lits: Vec<Lit> = search_target.lits_on_path(&path).iter()
                .map(|&l| l.clone()).collect();
            let mut full = pp.reconstruct_sat_assignment(path_lits);
            // Pad unmentioned vars with `var = false`.
            for v in 0..m.ast.vars.len() as u32 {
                if !full.iter().any(|l| l.var == v) {
                    full.push(Lit { var: v, neg: true });
                }
            }
            assert_eq!(m.nnf.evaluate(&full), Ok(true),
                "{}: reconstructed satisfying assignment {:?} does not satisfy F",
                formula, full);

            // Verify each emitted path-position translates to a valid
            // original-NNF leaf via pos_map.
            let positions = search_target.positions_on_path(&path);
            for p in &positions {
                let orig = pp.pos_map.translate(p)
                    .unwrap_or_else(|| panic!(
                        "{}: pos_map missing for search-target leaf {:?}", formula, p));
                assert!(m.nnf_complement.lit_at(&orig).is_some(),
                    "{}: translated position {:?} doesn't resolve to a leaf in m.nnf_complement",
                    formula, orig);
            }
        } else {
            // UNSAT: covers + lemma covers should dominate every comp path.
            let cover: crate::matrix::Cover = pp_classes.iter()
                .filter_map(|c| match c {
                    PathsClass::Covered(cp) => Some(cp.cover.clone()),
                    _ => None,
                }).collect();
            let translated = pp.reconstruct_cover(&cover);
            let original_comp = &m.nnf_complement;
            for path in original_comp.paths_iter() {
                let positions = original_comp.positions_on_path(&path);
                let covered = translated.iter().any(|(pa, pb)|
                    positions.contains(pa) && positions.contains(pb));
                assert!(covered,
                    "{}: translated cover {:?} misses comp path {:?}",
                    formula, translated, path);
            }
        }
    }

    #[test] fn preprocess_for_search_sat_unit() { preprocess_for_search_roundtrip("a", true); }
    #[test] fn preprocess_for_search_sat_with_pp() { preprocess_for_search_roundtrip("a (a' + b)", true); }
    #[test] fn preprocess_for_search_sat_or() { preprocess_for_search_roundtrip("a + b", true); }
    #[test] fn preprocess_for_search_unsat_contradiction() { preprocess_for_search_roundtrip("a a'", false); }
    #[test] fn preprocess_for_search_unsat_chain() { preprocess_for_search_roundtrip("a (a' + b) b'", false); }
    #[test] fn preprocess_for_search_unsat_three_clauses() {
        preprocess_for_search_roundtrip("a b (a' + b')", false);
    }

    // ─── Phase 3: BVE / at-most-1 collapse ───────────────────────────────

    /// 3-variable at-most-1 via sequential-counter encoding, plus an
    /// at-least-1 clause to make the formula SAT.  After BVE the
    /// formula is smaller and the SAT-witness reconstruction restores
    /// the eliminated variables (whichever they happen to be) such
    /// that the witness satisfies the original.
    ///
    /// Note: which specific variables BVE eliminates depends on the
    /// candidate-selection tiebreaker (min `p × n` then HashMap
    /// iteration order).  For this small artificial formula every
    /// variable has bounded occurrences, so BVE will eliminate
    /// several — we just require *some* eliminations + a correct
    /// round-trip.  On real formulas (faulty-adder, BMC) d-variables
    /// appear in non-clause-shaped Prod children (gate-definition
    /// implications), which makes them BVE-ineligible and forces
    /// BVE to pick the aux counter variables.
    #[test]
    fn bve_at_most_1_chain_simplifies_and_round_trips() {
        let formula = "(d1' + x1) (d2' + x2) (x1' + x2) (d2' + x1') (d3' + x2') (d1 + d2 + d3)";
        let m = Matrix::try_from(formula).unwrap();
        let pp = preprocess(&m.nnf);
        assert!(!pp.recon.is_empty(),
            "BVE should have eliminated at least one variable; recon={:?}", pp.recon);
        sat_roundtrip(formula, true);
    }

    /// At-most-1 + `d1 ∧ d2` (two d's forced true) — UNSAT.
    /// Round-trip the cover certificate.
    #[test]
    fn bve_at_most_1_with_unsat_unit_clauses() {
        let formula = "(d1' + x1) (d2' + x2) (x1' + x2) (d2' + x1') (d3' + x2') d1 d2";
        sat_roundtrip(formula, false);
    }

    /// Larger at-most-1 (5 d-vars, 4 aux) — verify reduction + round-trip.
    #[test]
    fn bve_at_most_1_five_vars_chain() {
        let formula = "(d1' + x1) \
                       (d2' + x2) (x1' + x2) (d2' + x1') \
                       (d3' + x3) (x2' + x3) (d3' + x2') \
                       (d4' + x4) (x3' + x4) (d4' + x3') \
                       (d5' + x4') \
                       (d1 + d2 + d3 + d4 + d5)";
        let m = Matrix::try_from(formula).unwrap();
        let pp = preprocess(&m.nnf);
        assert!(pp.recon.len() >= 4,
            "BVE should have eliminated at least 4 variables; recon depth={}",
            pp.recon.len());
        sat_roundtrip(formula, true);
    }

    /// d-variables that appear inside a non-clause-shaped Prod child
    /// (simulating a gate definition like `(d_i' ⇒ (a · b))`) are
    /// BVE-ineligible, so BVE preserves them and eliminates the aux
    /// counters instead — matching the behaviour we expect on real
    /// at-most-K formulas.
    #[test]
    fn bve_skips_d_vars_appearing_in_non_clause_shapes() {
        // At-most-1 chain + a "gate-def-like" clause for each d that
        // makes d appear in a Sum-with-Prod-child structure.
        let formula = "(d1' + x1) (d2' + x2) (x1' + x2) (d2' + x1') (d3' + x2') \
                       (d1 + d2 + d3) \
                       (d1' + a b) (d2' + a c) (d3' + a c')";
        let m = Matrix::try_from(formula).unwrap();
        let pp = preprocess(&m.nnf);
        let elim = pp.recon.eliminated_vars();
        let d1 = m.ast.var_index["d1"];
        let d2 = m.ast.var_index["d2"];
        let d3 = m.ast.var_index["d3"];
        assert!(!elim.contains(&d1), "d1 should NOT be BVE-eliminated (it appears in a non-clause-shape)");
        assert!(!elim.contains(&d2), "d2 should NOT be BVE-eliminated");
        assert!(!elim.contains(&d3), "d3 should NOT be BVE-eliminated");
        // x1 and/or x2 should be eliminated since they only appear in clause-shaped Prod children.
        let x1 = m.ast.var_index["x1"];
        let x2 = m.ast.var_index["x2"];
        assert!(elim.contains(&x1) || elim.contains(&x2),
            "at least one of x1/x2 should be eliminated by BVE; recon={:?}", pp.recon);
        sat_roundtrip(formula, true);
    }

    /// BVE recon's `Defined { defn }` must reference only surviving
    /// variables — chained aux eliminations should inline through
    /// resolution.  Verified by reconstructing a SAT witness.
    #[test]
    fn bve_defn_references_only_survivors() {
        // At-most-1 with 3 d's, then assert d2 (= satisfy exactly d2).
        let formula = "(d1' + x1) (d2' + x2) (x1' + x2) (d2' + x1') (d3' + x2') d2";
        let m = Matrix::try_from(formula).unwrap();
        let pp = preprocess(&m.nnf);
        // Any Defined step's defn should reference only surviving variables.
        let elim = pp.recon.eliminated_vars();
        for step in &pp.recon.steps {
            if let ReconStep::Defined { var, defn } = step {
                let mut vars_in_defn = Vec::new();
                collect_defn_vars(defn, &mut vars_in_defn);
                for v in &vars_in_defn {
                    if elim.contains(v) {
                        panic!("Defined({}) references eliminated var {}", var, v);
                    }
                }
            }
        }
        sat_roundtrip(formula, true);
    }

    fn collect_defn_vars(n: &NNF, out: &mut Vec<Var>) {
        match n {
            NNF::Lit(l) => out.push(l.var),
            NNF::Sum(ch) | NNF::Prod(ch) => for c in ch { collect_defn_vars(c, out); }
        }
    }

    // ─── Dual-framework reproducer ───
    //
    // The real reproducer lives in `src/dual/bench.rs` as
    // `dual_disagreement_on_faulty_add` (it needs the actual
    // faulty-adder formula via jq, which isn't accessible from this
    // test module).  Synthetic at-most-2 / at-most-K formulas
    // smaller than the real 16-stage faulty-adder don't reproduce
    // the disagreement — the bug requires enough simplified NNF
    // shape for CDCL's positions-on backjump (Some(1) return) to
    // skip the SAT subtree.  See `doc/preprocess.md` for the root
    // cause analysis.
}
