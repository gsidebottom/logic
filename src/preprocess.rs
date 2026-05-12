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
    /// `var := value` — forced unit literal.
    Unit { var: Var, value: bool },
    // Defined { var, defn } — Phase 4 (BVE).
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

    pub fn len(&self) -> usize { self.steps.len() }
    pub fn is_empty(&self) -> bool { self.steps.is_empty() }

    /// Extend a partial assignment over surviving variables with values
    /// for every variable eliminated during preprocessing.  Replayed
    /// in reverse insertion order so later definitions (Phase 4) can
    /// resolve against already-restored variables; Phase 1's `Unit`
    /// variants are independent so order doesn't matter.
    pub fn extend_assignment(&self, asgn: &mut Vec<Lit>) {
        for step in self.steps.iter().rev() {
            match step {
                ReconStep::Unit { var, value } => {
                    if !asgn.iter().any(|l| l.var == *var) {
                        // `value == true` ⇒ positive lit (neg = false).
                        asgn.push(Lit { var: *var, neg: !*value });
                    }
                }
            }
        }
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
}

// ─── Driver ────────────────────────────────────────────────────────────────

/// Phase 1 preprocessing: top-level unit propagation, run to fix-point.
pub fn preprocess(nnf: &NNF) -> Preprocessed {
    let mut tagged = NnfP::from_nnf(nnf);
    let mut recon = ReconstructionStack::new();
    let mut lemma_covers: Cover = Vec::new();

    loop {
        normalize(&mut tagged);

        match collect_top_units(&tagged) {
            UnitScan::None => break,
            UnitScan::Contradiction(pair) => {
                lemma_covers.push(pair);
                tagged = NnfP::Sum(vec![]); // false
                break;
            }
            UnitScan::Units { values, positions } => {
                for (var, value) in values.iter() {
                    recon.push_unit(*var, *value);
                }
                substitute_units(&mut tagged, &values, &positions, &mut lemma_covers);
                // Loop: re-normalize, look for newly-surfaced units.
            }
        }
    }

    let (nnf, fwd) = tagged.to_nnf_with_pos_map();
    Preprocessed {
        nnf,
        recon,
        pos_map: PositionMap { forward: fwd },
        lemma_covers,
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
    /// (padding unmentioned vars with `false`) and confirm it satisfies
    /// the *original* NNF.
    fn check_sat_witness(original: &NNF, comp_path_lits: Vec<Lit>, pp: &Preprocessed, num_vars: u32) {
        let mut full = pp.reconstruct_sat_assignment(comp_path_lits);
        // Pad unmentioned vars with `var = false`.
        for v in 0..num_vars {
            if !full.iter().any(|l| l.var == v) {
                full.push(Lit { var: v, neg: true });
            }
        }
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
}
