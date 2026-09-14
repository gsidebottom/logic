//! Box-aware matrix path search (`doc/box_backend_design.md` §3, §9).
//!
//! The matrix path search stays the driver, on the *collapsed* NNF where every
//! box call is an atom (`expand::atomize_box_calls`).  This wrapper controller
//! adds table propagation to any inner [`PathSearchController`]:
//!
//! * at every prefix step, each call whose atom is fixed on the prefix must
//!   keep at least one row consistent with the prefix (bit-parallel row
//!   masks; the "dead box → backtrack" rule of §3) — otherwise the prefix is
//!   pruned, exactly like a covered prefix;
//! * when a path completes, the rows of all fixed calls must be *jointly*
//!   consistent with the path (they may share variables that are not on the
//!   path) — checked exactly with the row engine — so an uncovered path is
//!   always a genuine model, and a Valid? / Satisfiable? run can stop at the
//!   first one.
//!
//! Polarity: a path literal is FALSE in the model it stands for, so the atom
//! literal `atom'` on a prefix means the call holds (rows of the box) and
//! `atom` that it fails (rows of the negation).  No CNF, no Tseitin, no
//! auxiliary variables: positions, covers and certificates keep their meaning.

use std::collections::HashMap;
use std::sync::Arc;

use crate::controller::PathSearchController;
use crate::matrix::{Lit, NNF, PathPrefix, PathsClass, ProdPath};
use super::{Engine, TableBox, Verdict};
use super::compile::implication_box;

/// One box call: the atom standing for it and its two tables over the
/// problem's variables (the call's arguments already bound).
pub struct CallBoxes {
    pub atom: u32,
    /// Rows of the box (the call holds).
    pub pos: TableBox,
    /// Rows of the box's negation (the call fails).
    pub neg: TableBox,
}

/// All calls of one formula, plus the variable count for the completion engine.
pub struct BoxTables {
    pub calls: Vec<CallBoxes>,
    /// Number of variables including call arguments that occur only inside calls.
    pub nvars: usize,
    /// The model the completion engine found for the last consistent complete
    /// path (its assignment, the model): [`witness`](Self::witness) returns
    /// it instead of solving again.
    pub memo: std::sync::Mutex<Option<Memo>>,
}

/// A remembered witness: a path's assignment and the engine's model for it.
pub type Memo = (HashMap<u32, bool>, Vec<bool>);

impl BoxTables {
    /// The partial model a prefix stands for (a path literal is FALSE), or
    /// `None` when the prefix already carries a complementary pair (covered
    /// by literals — left to the inner controller).
    pub fn assignment(prefix: &[&Lit]) -> Option<HashMap<u32, bool>> {
        let mut asg = HashMap::with_capacity(prefix.len());
        for l in prefix {
            if let Some(prev) = asg.insert(l.var, l.neg) && prev != l.neg { return None; }
        }
        Some(asg)
    }

    fn table_for<'a>(&'a self, c: &'a CallBoxes, asg: &HashMap<u32, bool>) -> Option<&'a TableBox> {
        asg.get(&c.atom).map(|&holds| if holds { &c.pos } else { &c.neg })
    }

    /// Cheap per-call check: every fixed call keeps a row consistent with `asg`.
    pub fn prefix_consistent(&self, asg: &HashMap<u32, bool>) -> bool {
        self.calls.iter().all(|c| match self.table_for(c, asg) {
            Some(t) => t.has_live_row(&|v| asg.get(&v).copied()),
            None => true,
        })
    }

    /// Exact joint check: the fixed calls' rows and `asg` together are
    /// satisfiable.  Returns the row engine's model (over all `nvars`) — the
    /// one remembered from the path search when `asg` is the path it completed.
    pub fn witness(&self, asg: &HashMap<u32, bool>) -> Option<Vec<bool>> {
        if let Ok(memo) = self.memo.lock() && let Some((a, m)) = memo.as_ref() && a == asg { return Some(m.clone()); }
        let units: Vec<Vec<i32>> = asg.iter()
            .map(|(&v, &b)| vec![if b { v as i32 + 1 } else { -(v as i32 + 1) }]).collect();
        let mut eng = Engine::from_cnf(self.nvars, &units);
        for c in &self.calls {
            if let Some(t) = self.table_for(c, asg) { eng.add_box(t.clone()); }
        }
        eng.max_decisions = Some(1_000_000);
        match eng.solve() { Verdict::Sat(m) => Some(m), _ => None }
    }
}

/// A call goes into the completion engine in clause form when its box has
/// at most this many rows …
pub const CLAUSE_FORM_MAX_ROWS: usize = 8;
/// … and its negation at most this many (each row of ¬B is one clause of B).
pub const CLAUSE_FORM_MAX_NEG_ROWS: usize = 4;

/// Wraps any controller with table propagation over the box calls.
pub struct BoxAwareController<Inner> {
    inner: Inner,
    tables: Arc<BoxTables>,
    /// One engine over every call's `atom ⇒ rows(B)` / `¬atom ⇒ rows(¬B)`
    /// tables, built once; completed paths are checked with `solve_under`.
    engine: Engine,
    engine_ok: bool,
    /// The previous prefix and its partial model (`Some(value)` per variable):
    /// a prefix is checked incrementally — "some row survives" is monotone in
    /// the assignment, so only the calls touched by literals beyond the common
    /// prefix with the previous one can have died.
    prev_prefix: Vec<Lit>,
    asg: Vec<Option<bool>>,
    /// var → calls whose atom it is or whose tables mention it.
    calls_of_var: Vec<Vec<u32>>,
    /// Prefixes pruned by the tables (dead box, or no joint row assignment).
    pub table_prunes: u64,
    // timing / counters, reported on drop when LOGIC_BOX_TIMING is set
    started: std::time::Instant,
    prefix_checks: u64,
    completions: u64,
    witness_time: std::time::Duration,
}

impl<Inner> BoxAwareController<Inner> {
    pub fn new(inner: Inner, tables: Arc<BoxTables>) -> Self {
        // A call whose tables are tiny goes in as clauses — `atom ⇒ B` is
        // one clause per row of ¬B, `¬atom ⇒ ¬B` one per row of B — which the
        // engine propagates with watched literals (visited only when a
        // watched literal is falsified, no live-row masks to update); larger
        // tables keep the mask form, whose propagation is stronger.
        let mut engine = Engine::new(tables.nvars, Vec::new());
        for c in &tables.calls {
            if c.pos.rows.len() <= CLAUSE_FORM_MAX_ROWS && c.neg.rows.len() <= CLAUSE_FORM_MAX_NEG_ROWS {
                let atom = |neg: bool| Lit { var: c.atom, neg };
                for row in &c.neg.rows {
                    let cl: Vec<Lit> = std::iter::once(atom(true)).chain(row.iter().map(|l| Lit { var: l.var, neg: !l.neg })).collect();
                    engine.add_clause(&cl);
                }
                for row in &c.pos.rows {
                    let cl: Vec<Lit> = std::iter::once(atom(false)).chain(row.iter().map(|l| Lit { var: l.var, neg: !l.neg })).collect();
                    engine.add_clause(&cl);
                }
            } else {
                engine.add_box(implication_box(c.pos.rows.clone(), c.atom, true));
                engine.add_box(implication_box(c.neg.rows.clone(), c.atom, false));
            }
        }
        let engine_ok = engine.init();
        let nvars = engine.nvars().max(tables.nvars);
        let mut calls_of_var: Vec<Vec<u32>> = vec![Vec::new(); nvars];
        for (ci, c) in tables.calls.iter().enumerate() {
            let mut vars: Vec<u32> = c.pos.vars.iter().chain(c.neg.vars.iter()).copied().chain(std::iter::once(c.atom)).collect();
            vars.sort_unstable(); vars.dedup();
            for v in vars { calls_of_var[v as usize].push(ci as u32); }
        }
        BoxAwareController { inner, tables, engine, engine_ok, prev_prefix: Vec::new(), asg: vec![None; nvars], calls_of_var,
            table_prunes: 0, started: std::time::Instant::now(), prefix_checks: 0, completions: 0, witness_time: std::time::Duration::ZERO }
    }

    /// Bring `asg` to the partial model of `prefix` (a path literal is FALSE
    /// in the model it stands for), returning the index of the first literal
    /// that is new relative to the previous prefix — or `None` when the prefix
    /// carries a complementary pair (covered by literals; the inner controller
    /// decides, and `asg` is left at the consistent part).
    fn update_assignment(&mut self, prefix: &[&Lit]) -> Option<usize> {
        let common = self.prev_prefix.iter().zip(prefix).take_while(|(a, b)| a.var == b.var && a.neg == b.neg).count();
        for l in &self.prev_prefix[common..] { self.asg[l.var as usize] = None; }
        self.prev_prefix.truncate(common);
        for l in &prefix[common..] {
            match self.asg[l.var as usize] {
                Some(v) if v != l.neg => return None,
                _ => { self.asg[l.var as usize] = Some(l.neg); self.prev_prefix.push(Lit { var: l.var, neg: l.neg }); }
            }
        }
        Some(common)
    }
}

impl<Inner> Drop for BoxAwareController<Inner> {
    fn drop(&mut self) {
        if std::env::var_os("LOGIC_BOX_TIMING").is_some() {
            eprintln!("[box-timing] search {:?}: {} prefix checks, {} completions, witness solves {:?}, {} table prunes; engine: {} decisions, {} propagations, {} conflicts",
                      self.started.elapsed(), self.prefix_checks, self.completions, self.witness_time, self.table_prunes,
                      self.engine.stats.decisions, self.engine.stats.propagations, self.engine.stats.conflicts);
        }
    }
}

impl<Inner: PathSearchController> PathSearchController for BoxAwareController<Inner> {
    type OnClass = ();

    fn set_cancel(&mut self, flag: std::sync::Arc<std::sync::atomic::AtomicBool>) {
        self.engine.cancel = Some(flag.clone());
        self.inner.set_cancel(flag);
    }

    fn should_continue_on_prefix(
        &mut self,
        prefix_literals: &Vec<&Lit>,
        prefix_positions: &PathPrefix,
        prefix_prod_path: &ProdPath,
        is_complete: bool,
    ) -> Option<usize> {
        self.prefix_checks += 1;
        if let Some(first_new) = self.update_assignment(prefix_literals) {
            // only the calls touched by the new literals can have lost their last live row
            for l in &prefix_literals[first_new..] {
                for k in 0..self.calls_of_var[l.var as usize].len() {
                    let c = &self.tables.calls[self.calls_of_var[l.var as usize][k] as usize];
                    let table = match self.asg[c.atom as usize] { Some(true) => &c.pos, Some(false) => &c.neg, None => continue };
                    if !table.has_live_row(&|v| self.asg[v as usize]) {
                        self.table_prunes += 1;
                        return Some(0);   // dead box: backtrack, like a covered prefix
                    }
                }
            }
            if is_complete {
                self.completions += 1;
                let t0 = std::time::Instant::now();
                // the path's literals are FALSE in the model it stands for
                let units: Vec<Lit> = prefix_literals.iter().map(|l| Lit { var: l.var, neg: !l.neg }).collect();
                let verdict = if self.engine_ok { self.engine.solve_under(&units) } else { Verdict::Unsat };
                self.witness_time += t0.elapsed();
                match verdict {
                    Verdict::Sat(model) => {
                        let asg: HashMap<u32, bool> = prefix_literals.iter().map(|l| (l.var, l.neg)).collect();
                        if let Ok(mut memo) = self.tables.memo.lock() { *memo = Some((asg, model)); }
                    }
                    Verdict::Unsat => { self.table_prunes += 1; return Some(0); }
                    Verdict::Unknown => return Some(0),   // cancelled (or out of budget): stop, the job is being discarded
                }
            }
        }
        self.inner.should_continue_on_prefix(prefix_literals, prefix_positions, prefix_prod_path, is_complete)
    }

    fn should_continue_on_paths_class(&mut self, paths_class: PathsClass, hit_limit: bool) -> bool {
        self.inner.should_continue_on_paths_class(paths_class, hit_limit)
    }
    fn needs_cover(&self) -> bool { self.inner.needs_cover() }
    fn sum_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.sum_ord(parent, children)
    }
    fn prod_ord<'a>(&mut self, parent: &'a NNF, children: &'a [NNF]) -> Option<Vec<(usize, &'a NNF)>> {
        self.inner.prod_ord(parent, children)
    }
    fn path_count(&self) -> usize { self.inner.path_count() }
    fn covered_prefix_count(&self) -> usize { self.inner.covered_prefix_count() }
    fn uncovered_path_count(&self) -> usize { self.inner.uncovered_path_count() }
    fn paths_classified(&self) -> f64 { self.inner.paths_classified() }
    fn pre_leaf_pruning_credit(&self) -> f64 { self.inner.pre_leaf_pruning_credit() }
    fn cdcl_conflict_count(&self) -> usize { self.inner.cdcl_conflict_count() }
    fn cdcl_restart_count(&self) -> usize { self.inner.cdcl_restart_count() }
    fn is_restart_pending(&self) -> bool { self.inner.is_restart_pending() }
    fn complete_restart(&mut self) { self.inner.complete_restart(); }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::matrix::{default_classify_controller, Matrix, PathParams};

    /// Uncovered paths of `text`'s NNF, with (or without) the tables.
    fn uncovered(text: &str, tables: Option<Arc<BoxTables>>) -> Vec<Vec<Lit>> {
        let m = Matrix::try_from(text).unwrap();
        let nnf = m.nnf.clone();
        let rt = tokio::runtime::Runtime::new().unwrap();
        rt.block_on(async move {
            let params = Some(PathParams { paths_class_limit: usize::MAX, ..Default::default() });
            let (h, mut rx, _c) = match tables {
                Some(t) => nnf.classify_paths(64, move |tx| BoxAwareController::new(default_classify_controller(params, tx), t)),
                None => nnf.classify_paths(64, move |tx| default_classify_controller(params, tx)),
            };
            let mut out = Vec::new();
            while let Some((class, _)) = rx.recv().await {
                if let PathsClass::Uncovered(up) = class {
                    out.push(m.nnf.lits_on_path(&up.prod_path).iter().map(|&l| l.clone()).collect());
                }
            }
            let _ = h.await;
            out
        })
    }

    fn lit(v: u32, neg: bool) -> Lit { Lit { var: v, neg } }

    #[test]
    fn tables_prune_spurious_paths_and_keep_models() {
        // A stands for eq(x, y).  Searching NNF(A' + (x = y)) = NNF(¬(eq ∧ (x ⊕ y)))
        // enumerates the models of eq(x,y) ∧ (x ⊕ y): none — but without the
        // table two paths look uncovered.
        let m = Matrix::try_from("A' + (x = y)").unwrap();
        let (a, x, y) = (m.ast.var_index["A"], m.ast.var_index["x"], m.ast.var_index["y"]);
        let eq = BoxTables { nvars: 3, memo: std::sync::Mutex::new(None), calls: vec![CallBoxes {
            atom: a,
            pos: TableBox::new(vec![vec![lit(x, false), lit(y, false)], vec![lit(x, true), lit(y, true)]]),
            neg: TableBox::new(vec![vec![lit(x, false), lit(y, true)], vec![lit(x, true), lit(y, false)]]),
        }]};
        let eq = Arc::new(eq);
        assert_eq!(uncovered("A' + (x = y)", None).len(), 2);
        assert_eq!(uncovered("A' + (x = y)", Some(eq.clone())).len(), 0);
        // eq(x,y) ∧ x is satisfiable: NNF(A' + x') has one path, consistent
        // with the table (x = y = 1), and the witness fills in y.
        let paths = uncovered("A' + x'", Some(eq.clone()));
        assert_eq!(paths.len(), 1);
        let asg = BoxTables::assignment(&paths[0].iter().collect::<Vec<_>>()).unwrap();
        let model = eq.witness(&asg).unwrap();
        assert!(model[a as usize] && model[x as usize] && model[y as usize]);
        // ¬eq(x,y) ∧ x: the path {A, x'} fixes the call FALSE → rows of the
        // negation → y = 0.
        let paths = uncovered("A + x'", Some(eq.clone()));
        assert_eq!(paths.len(), 1);
        let asg = BoxTables::assignment(&paths[0].iter().collect::<Vec<_>>()).unwrap();
        let model = eq.witness(&asg).unwrap();
        assert!(!model[a as usize] && model[x as usize] && !model[y as usize]);
    }
}
