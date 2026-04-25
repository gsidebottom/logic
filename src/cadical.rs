use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use crate::matrix::{PathClassificationHandle, Lit, Matrix, NNF};

// ─── Tseitin encoding ────────────────────────────────────────────────────────

/// Tseitin encoding: convert an NNF to CNF clauses for CaDiCaL.
/// Variable numbering: original vars are 1-based (var+1).
/// Auxiliary vars start at `next_var`. Returns (root_var, clauses).
pub fn tseitin_encode(nnf: &NNF, next_var: &mut i32) -> (i32, Vec<Vec<i32>>) {
    let mut clauses = Vec::new();
    match nnf {
        NNF::Lit(l) => {
            let v = (l.var as i32) + 1;
            (if l.neg { -v } else { v }, clauses)
        }
        NNF::Prod(ch) => {
            // AND gate: root ↔ (c1 ∧ c2 ∧ ... ∧ cn)
            let root = *next_var; *next_var += 1;
            let mut child_vars = Vec::new();
            for c in ch {
                let (cv, mut cc) = tseitin_encode(c, next_var);
                clauses.append(&mut cc);
                child_vars.push(cv);
            }
            // root → ci  for each i:  (-root ∨ ci)
            for &cv in &child_vars {
                clauses.push(vec![-root, cv]);
            }
            // c1 ∧ c2 ∧ ... ∧ cn → root:  (-c1 ∨ -c2 ∨ ... ∨ -cn ∨ root)
            let mut clause: Vec<i32> = child_vars.iter().map(|&cv| -cv).collect();
            clause.push(root);
            clauses.push(clause);
            (root, clauses)
        }
        NNF::Sum(ch) => {
            // OR gate: root ↔ (c1 ∨ c2 ∨ ... ∨ cn)
            let root = *next_var; *next_var += 1;
            let mut child_vars = Vec::new();
            for c in ch {
                let (cv, mut cc) = tseitin_encode(c, next_var);
                clauses.append(&mut cc);
                child_vars.push(cv);
            }
            // ci → root  for each i:  (-ci ∨ root)
            for &cv in &child_vars {
                clauses.push(vec![-cv, root]);
            }
            // root → c1 ∨ c2 ∨ ... ∨ cn:  (-root ∨ c1 ∨ c2 ∨ ... ∨ cn)
            let mut clause = vec![-root];
            clause.extend_from_slice(&child_vars);
            clauses.push(clause);
            (root, clauses)
        }
    }
}

// ─── Callbacks ───────────────────────────────────────────────────────────────

struct SolverCallbacks {
    cancel: Arc<AtomicBool>,
    learned_clauses: Vec<Vec<i32>>,
}

impl cadical::Callbacks for SolverCallbacks {
    fn max_length(&self) -> i32 { i32::MAX }

    fn learn(&mut self, clause: &[i32]) {
        self.learned_clauses.push(clause.to_vec());
    }

    fn terminate(&mut self) -> bool {
        self.cancel.load(Ordering::Relaxed)
    }
}

// ─── Result types ────────────────────────────────────────────────────────────

pub struct CaDiCaLValidResult {
    pub result: Result<(), Vec<Lit>>,
    pub learned_clauses: Vec<Vec<i32>>,
}

pub struct CaDiCaLSatisfiableResult {
    pub result: Result<Vec<Lit>, ()>,
    pub learned_clauses: Vec<Vec<i32>>,
}

// ─── Extract assignment from solver ──────────────────────────────────────────

fn extract_assignment(solver: &cadical::Solver<SolverCallbacks>, n_vars: i32) -> Vec<Lit> {
    (0..n_vars as u32).filter_map(|v| {
        solver.value((v as i32) + 1).map(|val|
            if val { Lit::pos(v) } else { Lit::neg(v) }
        )
    }).collect()
}

// ─── Matrix methods ──────────────────────────────────────────────────────────

impl Matrix {
    /// Check validity using CaDiCaL. Valid iff the complement is unsatisfiable.
    /// Returns a JoinHandle and PathClassificationHandle for async cancellation.
    pub fn cadical_valid(&self) -> (
        tokio::task::JoinHandle<Result<CaDiCaLValidResult, Box<dyn std::error::Error + Send>>>,
        PathClassificationHandle,
    ) {
        let nnf_complement = self.nnf_complement.clone();
        let n_vars = self.ast.vars.len() as i32;
        let cancel = PathClassificationHandle::new();
        let cancel_inner = Arc::new(AtomicBool::new(false));
        let cancel_for_callback = cancel_inner.clone();
        let cancel_handle = cancel.clone();

        let handle = tokio::task::spawn_blocking(move || {
            let mut next_var = n_vars + 1;
            let (root, clauses) = tseitin_encode(&nnf_complement, &mut next_var);
            let mut solver: cadical::Solver<SolverCallbacks> = cadical::Solver::new();
            solver.set_callbacks(Some(SolverCallbacks {
                cancel: cancel_for_callback,
                learned_clauses: Vec::new(),
            }));
            for clause in &clauses { solver.add_clause(clause.iter().copied()); }
            solver.add_clause([root]);

            let sat = solver.solve();

            let learned_clauses = solver.get_callbacks().as_ref()
                .map(|cb| cb.learned_clauses.clone())
                .unwrap_or_default();

            match sat {
                Some(true) => {
                    // Complement is satisfiable → not valid → falsifying assignment
                    let asgn = extract_assignment(&solver, n_vars);
                    Ok(CaDiCaLValidResult {
                        result: Err(asgn),
                        learned_clauses,
                    })
                }
                Some(false) => {
                    Ok(CaDiCaLValidResult {
                        result: Ok(()),
                        learned_clauses,
                    })
                }
                None => Err(Box::new(std::io::Error::new(std::io::ErrorKind::Interrupted, "cadical: resource exhaustion or cancelled")) as Box<dyn std::error::Error + Send>),
            }
        });

        // Spawn a watcher that propagates PathClassificationHandle to the AtomicBool
        let cancel_flag = cancel_inner;
        let cancel_watch = cancel_handle.clone();
        tokio::task::spawn(async move {
            loop {
                if cancel_watch.is_cancelled() {
                    cancel_flag.store(true, Ordering::Relaxed);
                    break;
                }
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            }
        });

        (handle, cancel_handle)
    }

    /// Check satisfiability using CaDiCaL.
    /// Returns a JoinHandle and PathClassificationHandle for async cancellation.
    pub fn cadical_satisfiable(&self) -> (
        tokio::task::JoinHandle<Result<CaDiCaLSatisfiableResult, Box<dyn std::error::Error + Send>>>,
        PathClassificationHandle,
    ) {
        let nnf = self.nnf.clone();
        let n_vars = self.ast.vars.len() as i32;
        let cancel = PathClassificationHandle::new();
        let cancel_inner = Arc::new(AtomicBool::new(false));
        let cancel_for_callback = cancel_inner.clone();
        let cancel_handle = cancel.clone();

        let handle = tokio::task::spawn_blocking(move || {
            let mut next_var = n_vars + 1;
            let (root, clauses) = tseitin_encode(&nnf, &mut next_var);
            let mut solver: cadical::Solver<SolverCallbacks> = cadical::Solver::new();
            solver.set_callbacks(Some(SolverCallbacks {
                cancel: cancel_for_callback,
                learned_clauses: Vec::new(),
            }));
            for clause in &clauses { solver.add_clause(clause.iter().copied()); }
            solver.add_clause([root]);

            let sat = solver.solve();

            let learned_clauses = solver.get_callbacks().as_ref()
                .map(|cb| cb.learned_clauses.clone())
                .unwrap_or_default();

            match sat {
                Some(true) => {
                    let asgn = extract_assignment(&solver, n_vars);
                    Ok(CaDiCaLSatisfiableResult {
                        result: Ok(asgn),
                        learned_clauses,
                    })
                }
                Some(false) => {
                    Ok(CaDiCaLSatisfiableResult {
                        result: Err(()),
                        learned_clauses,
                    })
                }
                None => Err(Box::new(std::io::Error::new(std::io::ErrorKind::Interrupted, "cadical: resource exhaustion or cancelled")) as Box<dyn std::error::Error + Send>),
            }
        });

        let cancel_flag = cancel_inner;
        let cancel_watch = cancel_handle.clone();
        tokio::task::spawn(async move {
            loop {
                if cancel_watch.is_cancelled() {
                    cancel_flag.store(true, Ordering::Relaxed);
                    break;
                }
                tokio::time::sleep(std::time::Duration::from_millis(10)).await;
            }
        });

        (handle, cancel_handle)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sat_11_var_single_product() {
        let formula = "(a_10' a_9' a_8' a_7' a_6 a_5 a_4 a_3' a_2 a_1 a_0)";
        let m = Matrix::try_from(formula).unwrap();
        let vars = m.ast.vars.clone();

        let rt = tokio::runtime::Runtime::new().expect("failed to create tokio runtime");
        let result = rt.block_on(async {
            let (handle, _cancel) = m.cadical_satisfiable();
            handle.await.expect("sat task panicked").expect("cadical sat failed")
        });

        let asgn = result.result.expect("formula should be satisfiable");

        // Expected assignment:
        // a_10=0, a_9=0, a_8=0, a_7=0, a_6=1, a_5=1, a_4=1, a_3=0, a_2=1, a_1=1, a_0=1.
        let expected: &[(&str, bool)] = &[
            ("a_10", false), ("a_9", false), ("a_8", false), ("a_7", false),
            ("a_6",  true),  ("a_5", true),  ("a_4", true),
            ("a_3",  false),
            ("a_2",  true),  ("a_1", true),  ("a_0", true),
        ];
        for (name, want) in expected {
            let idx = vars.iter().position(|v| v == name)
                .unwrap_or_else(|| panic!("variable {} not in formula", name));
            let lit = asgn.iter().find(|l| l.var as usize == idx)
                .unwrap_or_else(|| panic!("no assignment for {}", name));
            let got = !lit.neg; // neg=false means positive → true
            assert_eq!(got, *want, "{} = {} but expected {}", name, got, want);
        }
    }
}
