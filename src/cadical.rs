use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};
use crate::matrix::{CancelHandle, Lit, Matrix, NNF};
use crate::simplify::{qmc, minimal_cover};

// ─── NNF to CNF conversion (no auxiliary variables) ──────────────────────────

/// Convert an NNF to CNF clauses using maxterm enumeration + QMC minimization.
/// Returns clauses using 1-based variable numbering (positive = true, negative = negated).
/// Only uses original variables — no auxiliary Tseitin variables.
///
/// Panics if n > 30 (2^30 assignments would be too many to enumerate).
pub fn nnf_to_cnf_clauses(nnf: &NNF, n: usize) -> Vec<Vec<i32>> {
    assert!(n <= 30, "nnf_to_cnf_clauses: too many variables ({}) for exhaustive enumeration", n);

    if n == 0 {
        // Evaluate with empty assignment
        return match nnf.evaluate(&[]) {
            Ok(true) => vec![],          // tautology: no clauses needed
            Ok(false) => vec![vec![]],   // contradiction: empty clause
            Err(()) => vec![],           // undetermined with no vars — treat as true
        };
    }

    // Find maxterms: assignments where the formula evaluates to FALSE.
    let mut maxterms = Vec::new();
    for i in 0..(1usize << n) {
        let asgn: Vec<Lit> = (0..n as u32).map(|j| {
            if (i >> (n - 1 - j as usize)) & 1 == 1 { Lit::pos(j) } else { Lit::neg(j) }
        }).collect();
        if nnf.evaluate(&asgn) == Ok(false) {
            maxterms.push(i);
        }
    }

    if maxterms.is_empty() { return vec![]; }           // tautology
    if maxterms.len() == 1 << n { return vec![vec![]]; } // contradiction

    // Run QMC on the maxterms to get prime implicants of the negation.
    let primes = qmc(&maxterms, n);
    let cover = minimal_cover(&primes, &maxterms);

    // Convert each implicant to a clause (De Morgan: maxterm → disjunction).
    // In a maxterm assignment, bit=0 → positive literal in clause, bit=1 → negative.
    cover.iter().map(|imp| {
        (0..n).filter_map(|j| {
            let var = (j as i32) + 1; // 1-based
            match imp.term[j] {
                0 => Some(var),   // false in maxterm → positive in clause
                1 => Some(-var),  // true in maxterm → negative in clause
                _ => None,        // don't-care: omit
            }
        }).collect()
    }).collect()
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
    /// Returns a JoinHandle and CancelHandle for async cancellation.
    pub fn cadical_valid(&self) -> (
        tokio::task::JoinHandle<Result<CaDiCaLValidResult, Box<dyn std::error::Error + Send>>>,
        CancelHandle,
    ) {
        let nnf_complement = self.nnf_complement.clone();
        let n_vars = self.ast.vars.len();
        let cancel = CancelHandle::new();
        let cancel_inner = Arc::new(AtomicBool::new(false));
        let cancel_for_callback = cancel_inner.clone();
        let cancel_handle = cancel.clone();

        let handle = tokio::task::spawn_blocking(move || {
            let clauses = nnf_to_cnf_clauses(&nnf_complement, n_vars);
            let mut solver: cadical::Solver<SolverCallbacks> = cadical::Solver::new();
            solver.set_callbacks(Some(SolverCallbacks {
                cancel: cancel_for_callback,
                learned_clauses: Vec::new(),
            }));
            for clause in &clauses { solver.add_clause(clause.iter().copied()); }

            let sat = solver.solve();

            let learned_clauses = solver.get_callbacks().as_ref()
                .map(|cb| cb.learned_clauses.clone())
                .unwrap_or_default();

            match sat {
                Some(true) => {
                    // Complement is satisfiable → not valid → falsifying assignment
                    let asgn = extract_assignment(&solver, n_vars as i32);
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

        // Spawn a watcher that propagates CancelHandle to the AtomicBool
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
    /// Returns a JoinHandle and CancelHandle for async cancellation.
    pub fn cadical_satisfiable(&self) -> (
        tokio::task::JoinHandle<Result<CaDiCaLSatisfiableResult, Box<dyn std::error::Error + Send>>>,
        CancelHandle,
    ) {
        let nnf = self.nnf.clone();
        let n_vars = self.ast.vars.len();
        let cancel = CancelHandle::new();
        let cancel_inner = Arc::new(AtomicBool::new(false));
        let cancel_for_callback = cancel_inner.clone();
        let cancel_handle = cancel.clone();

        let handle = tokio::task::spawn_blocking(move || {
            let clauses = nnf_to_cnf_clauses(&nnf, n_vars);
            let mut solver: cadical::Solver<SolverCallbacks> = cadical::Solver::new();
            solver.set_callbacks(Some(SolverCallbacks {
                cancel: cancel_for_callback,
                learned_clauses: Vec::new(),
            }));
            for clause in &clauses { solver.add_clause(clause.iter().copied()); }

            let sat = solver.solve();

            let learned_clauses = solver.get_callbacks().as_ref()
                .map(|cb| cb.learned_clauses.clone())
                .unwrap_or_default();

            match sat {
                Some(true) => {
                    let asgn = extract_assignment(&solver, n_vars as i32);
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
