//! Table boxes as a CaDiCaL external propagator (IPASIR-UP): the box
//! engine's propagation -- live-row masks cut down by kill masks, forced
//! literals, lazily explained by a cover of the dead rows -- running
//! inside CaDiCaL's CDCL core instead of ours.  Everything here is over
//! DIMACS literals; the boxes' variables are 0-based as in `TableBox`.
use super::{Lit, TableBox};
use crate::cadical::solver::Propagator;

pub struct BoxPropagator {
    boxes: Vec<TableBox>,
    /// Per box: DIMACS variables in local-index order; live-mask offset;
    /// words per mask; the mask of all rows.
    vars: Vec<Vec<i32>>,
    off: Vec<usize>,
    nw: Vec<usize>,
    full: Vec<Vec<u64>>,
    live: Vec<u64>,
    /// Per DIMACS variable: the boxes it is in, with its local index.
    occ: Vec<Vec<(u32, u32)>>,
    /// Per DIMACS variable: 0 unassigned, 1 true, -1 false.
    val: Vec<i8>,
    trail: Vec<i32>,
    /// `level_start[k]`: the trail length when decision level k began (k >= 1).
    level_start: Vec<usize>,
    /// Undo log: (box, its live words before the first kill at a level),
    /// with the log length when each level began.
    undo: Vec<(u32, Vec<u64>)>,
    undo_start: Vec<usize>,
    /// Per box: the level of its latest snapshot (usize::MAX for none).
    snap_level: Vec<usize>,
    touched: Vec<u32>,
    in_touched: Vec<bool>,
    /// A dead box whose conflict clause is owed.
    dead: Option<u32>,
    /// Per variable: proposed to CaDiCaL and not yet notified back; the box
    /// that forced it and the trail length at that moment (the reason may
    /// only use literals assigned before the propagation).
    proposed: Vec<bool>,
    reason_box: Vec<u32>,
    reason_trail: Vec<usize>,
    pub propagations: u64,
    pub conflicts: u64,
    pub reasons: u64,
    pub reason_lits: u64,
}

impl BoxPropagator {
    /// `boxes` over 0-based variables, as `TableBox` holds them.
    pub fn new(boxes: Vec<TableBox>) -> BoxPropagator {
        let maxvar = boxes.iter().flat_map(|b| b.vars.iter()).map(|&v| v as usize + 1).max().unwrap_or(0);
        let mut p = BoxPropagator {
            vars: Vec::new(), off: Vec::new(), nw: Vec::new(), full: Vec::new(), live: Vec::new(),
            occ: vec![Vec::new(); maxvar + 1], val: vec![0; maxvar + 1], trail: Vec::new(),
            level_start: vec![0], undo: Vec::new(), undo_start: vec![0], snap_level: Vec::new(),
            touched: Vec::new(), in_touched: Vec::new(), dead: None,
            proposed: vec![false; maxvar + 1], reason_box: vec![0; maxvar + 1], reason_trail: vec![0; maxvar + 1],
            propagations: 0, conflicts: 0, reasons: 0, reason_lits: 0, boxes: Vec::new(),
        };
        for (bi, b) in boxes.iter().enumerate() {
            let nw = b.nwords();
            let nrows = b.rows.len();
            let mut full = vec![0u64; nw];
            for r in 0..nrows { full[r / 64] |= 1u64 << (r % 64); }
            p.off.push(p.live.len());
            p.live.extend_from_slice(&full);
            p.full.push(full);
            p.nw.push(nw);
            p.vars.push(b.vars.iter().map(|&v| v as i32 + 1).collect());
            for (li, &v) in b.vars.iter().enumerate() { p.occ[v as usize + 1].push((bi as u32, li as u32)); }
            p.snap_level.push(usize::MAX);
            p.in_touched.push(true);
            p.touched.push(bi as u32);   // examined once before any assignment: a box may force at root
        }
        p.boxes = boxes;
        p
    }

    /// The DIMACS variables CaDiCaL must observe.
    pub fn observed_vars(&self) -> Vec<i32> {
        (1..self.occ.len()).filter(|&v| !self.occ[v].is_empty()).map(|v| v as i32).collect()
    }

    fn level(&self) -> usize { self.level_start.len() - 1 }

    fn kill(&mut self, b: usize, li: usize, value: bool) {
        let lvl = self.level();
        if self.snap_level[b] != lvl {
            let (off, nw) = (self.off[b], self.nw[b]);
            self.undo.push((b as u32, self.live[off..off + nw].to_vec()));
            self.snap_level[b] = lvl;
        }
        let (off, nw) = (self.off[b], self.nw[b]);
        let k = self.boxes[b].kill_rows(li, value);
        for (l, &kw) in self.live[off..off + nw].iter_mut().zip(k.iter()) { *l &= !kw; }
        if !self.in_touched[b] { self.in_touched[b] = true; self.touched.push(b as u32); }
    }

    /// The assigned literals of box `b` among `trail[..limit]`, in trail
    /// order, whose kills together cover `target`; pushed negated onto
    /// `out`.  Every row of `target` must be dead.
    fn cover(&self, b: usize, limit: usize, mut target: Vec<u64>, out: &mut Vec<i32>) {
        let nw = self.nw[b];
        for &lit in &self.trail[..limit] {
            if target.iter().all(|&w| w == 0) { break; }
            let v = lit.unsigned_abs() as usize;
            for &(bb, li) in &self.occ[v] {
                if bb as usize != b { continue; }
                let k = self.boxes[b].kill_rows(li as usize, lit > 0);
                if (0..nw).any(|w| target[w] & k[w] != 0) {
                    out.push(-lit);
                    for w in 0..nw { target[w] &= !k[w]; }
                }
            }
        }
        debug_assert!(target.iter().all(|&w| w == 0), "dead rows not covered by the assignment");
    }
}

impl Propagator for BoxPropagator {
    fn notify_assignment(&mut self, lits: &[i32]) {
        for &lit in lits {
            let v = lit.unsigned_abs() as usize;
            if v >= self.val.len() || self.val[v] != 0 { continue; }
            self.val[v] = if lit > 0 { 1 } else { -1 };
            self.proposed[v] = false;
            self.trail.push(lit);
            let occ = std::mem::take(&mut self.occ[v]);
            for &(b, li) in &occ { self.kill(b as usize, li as usize, lit > 0); }
            self.occ[v] = occ;
        }
    }

    fn notify_new_decision_level(&mut self) {
        self.level_start.push(self.trail.len());
        self.undo_start.push(self.undo.len());
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        if new_level + 1 >= self.level_start.len() { return; }
        let keep = self.level_start[new_level + 1];
        for &lit in &self.trail[keep..] { let v = lit.unsigned_abs() as usize; self.val[v] = 0; self.proposed[v] = false; }
        self.trail.truncate(keep);
        let ukeep = self.undo_start[new_level + 1];
        while self.undo.len() > ukeep {
            let (b, old) = self.undo.pop().unwrap();
            let (off, nw) = (self.off[b as usize], self.nw[b as usize]);
            self.live[off..off + nw].copy_from_slice(&old);
            self.snap_level[b as usize] = usize::MAX;
        }
        self.level_start.truncate(new_level + 1);
        self.undo_start.truncate(new_level + 1);
        for &b in &self.touched { self.in_touched[b as usize] = false; }
        self.touched.clear();
        self.dead = None;
    }

    fn check_found_model(&mut self, model: &[i32]) -> bool {
        let mut m = vec![0i8; self.val.len()];
        for &lit in model { let v = lit.unsigned_abs() as usize; if v < m.len() { m[v] = if lit > 0 { 1 } else { -1 }; } }
        let holds = |l: &Lit| m[l.var as usize + 1] == if l.neg { -1 } else { 1 };
        self.boxes.iter().all(|b| b.rows.iter().any(|r| r.iter().all(holds)))
    }

    fn propagate(&mut self) -> i32 {
        if self.dead.is_some() { return 0; }
        while let Some(b) = self.touched.pop() {
            let b = b as usize;
            self.in_touched[b] = false;
            let (off, nw) = (self.off[b], self.nw[b]);
            if (0..nw).all(|w| self.live[off + w] == 0) {
                self.dead = Some(b as u32);
                self.conflicts += 1;
                return 0;
            }
            for li in 0..self.vars[b].len() {
                let v = self.vars[b][li];
                if self.val[v as usize] != 0 || self.proposed[v as usize] { continue; }
                // every live row has the variable TRUE  <=>  assigning FALSE kills them all
                let kf = self.boxes[b].kill_rows(li, false);
                let kt = self.boxes[b].kill_rows(li, true);
                let forced = if (0..nw).all(|w| self.live[off + w] & !kf[w] == 0) { Some(true) }
                             else if (0..nw).all(|w| self.live[off + w] & !kt[w] == 0) { Some(false) }
                             else { None };
                if let Some(value) = forced {
                    self.proposed[v as usize] = true;
                    self.reason_box[v as usize] = b as u32;
                    self.reason_trail[v as usize] = self.trail.len();
                    self.propagations += 1;
                    // the box has more to say, perhaps: look at it again
                    if !self.in_touched[b] { self.in_touched[b] = true; self.touched.push(b as u32); }
                    return if value { v } else { -v };
                }
            }
        }
        0
    }

    fn reason(&mut self, lit: i32, out: &mut Vec<i32>) {
        let v = lit.unsigned_abs() as usize;
        let b = self.reason_box[v] as usize;
        let li = self.vars[b].iter().position(|&x| x == v as i32).expect("propagated variable not in its box");
        // forced TRUE: the rows with the variable FALSE (or unmentioned) are all dead
        let k = self.boxes[b].kill_rows(li, lit < 0);   // rows that die when assigned the OTHER value == rows where it is `lit`'s value
        let nw = self.nw[b];
        let target: Vec<u64> = (0..nw).map(|w| self.full[b][w] & !k[w]).collect();
        out.clear();
        out.push(lit);
        self.cover(b, self.reason_trail[v], target, out);
        self.reasons += 1;
        self.reason_lits += out.len() as u64;
    }

    fn external_clause(&mut self, out: &mut Vec<i32>) -> bool {
        let Some(b) = self.dead.take() else { return false };
        let b = b as usize;
        out.clear();
        let target = self.full[b].clone();
        self.cover(b, self.trail.len(), target, out);
        true
    }

    fn report(&self) -> String {
        format!("c cadical: boxes through the external propagator: {} propagations, {} box conflicts, {} reasons of {:.2} literals",
                self.propagations, self.conflicts, self.reasons, self.reason_lits as f64 / self.reasons.max(1) as f64)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cadical;

    fn check_model(cls: &[Vec<i32>], m: &[bool]) -> bool {
        cls.iter().all(|c| c.iter().any(|&l| m[l.unsigned_abs() as usize - 1] == (l > 0)))
    }

    /// The same instances with the tables propagated natively inside
    /// CaDiCaL (`Solver::add_table`).
    #[test]
    fn random_tables_vs_bruteforce_native_in_cadical() {
        let mut seed: u64 = 0x1234_5678_9ABC_DEF1;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for trial in 0..400 {
            let n = 3 + (rnd() % 6) as usize;
            let nboxes = 1 + (rnd() % 5) as usize;
            let mut boxes: Vec<Vec<Vec<Lit>>> = Vec::new();
            for _ in 0..nboxes {
                let k = 2 + (rnd() % 3) as usize;
                let mut cols: Vec<u32> = Vec::new();
                while cols.len() < k.min(n) { let v = (rnd() % n as u64) as u32; if !cols.contains(&v) { cols.push(v); } }
                let nrows = 1 + (rnd() % 5) as usize;
                let mut rows: Vec<Vec<Lit>> = Vec::new();
                for _ in 0..nrows {
                    let mut row = Vec::new();
                    for &v in &cols { if rnd() % 3 != 0 { let neg = rnd() % 2 == 0; row.push(Lit { var: v, neg }); } }
                    rows.push(row);
                }
                boxes.push(rows);
            }
            let nclauses = (rnd() % 4) as usize;
            let cls: Vec<Vec<i32>> = (0..nclauses).map(|_| (0..3).map(|_| { let v = (rnd() % n as u64) as i32 + 1; if rnd() % 2 == 0 { v } else { -v } }).collect()).collect();
            let row_holds = |row: &[Lit], m: &[bool]| row.iter().all(|l| m[l.var as usize] != l.neg);
            let holds = |m: &[bool]| boxes.iter().all(|rows| rows.iter().any(|r| row_holds(r, m))) && check_model(&cls, m);
            let brute = (0..1u32 << n).any(|bits| holds(&(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let mut solver: cadical::Solver = cadical::Solver::new();
            solver.reserve(n as i32);
            for c in &cls { solver.add_clause(c.iter().copied()); }
            for rows in &boxes {
                let t = TableBox::new(rows.clone());
                let vars: Vec<i32> = t.vars.iter().map(|&v| v as i32 + 1).collect();
                let trows: Vec<Vec<i32>> = t.rows.iter().map(|r| r.iter().map(|l| if l.neg { -(l.var as i32 + 1) } else { l.var as i32 + 1 }).collect()).collect();
                solver.add_table(&vars, &trows);
            }
            match solver.solve() {
                Some(true) => {
                    let m: Vec<bool> = (1..=n as i32).map(|v| solver.value(v).unwrap_or(true)).collect();
                    assert!(brute, "trial {trial}: native tables SAT, brute UNSAT: {boxes:?} {cls:?}");
                    assert!(holds(&m), "trial {trial}: bad model {m:?} for {boxes:?} {cls:?}");
                }
                Some(false) => assert!(!brute, "trial {trial}: native tables UNSAT, brute SAT: {boxes:?} {cls:?}"),
                None => panic!("no budget set"),
            }
        }
    }

    /// Random tables and clauses through CaDiCaL with the propagator,
    /// against brute force -- the box engine's own test, on the other core.
    #[test]
    fn random_tables_vs_bruteforce_in_cadical() {
        let mut seed: u64 = 0x1234_5678_9ABC_DEF1;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for trial in 0..400 {
            let n = 3 + (rnd() % 6) as usize;
            let nboxes = 1 + (rnd() % 5) as usize;
            let mut boxes: Vec<Vec<Vec<Lit>>> = Vec::new();
            for _ in 0..nboxes {
                let k = 2 + (rnd() % 3) as usize;
                let mut cols: Vec<u32> = Vec::new();
                while cols.len() < k.min(n) { let v = (rnd() % n as u64) as u32; if !cols.contains(&v) { cols.push(v); } }
                let nrows = 1 + (rnd() % 5) as usize;
                let mut rows: Vec<Vec<Lit>> = Vec::new();
                for _ in 0..nrows {
                    let mut row = Vec::new();
                    for &v in &cols { if rnd() % 3 != 0 { let neg = rnd() % 2 == 0; row.push(Lit { var: v, neg }); } }
                    rows.push(row);
                }
                boxes.push(rows);
            }
            let nclauses = (rnd() % 4) as usize;
            let cls: Vec<Vec<i32>> = (0..nclauses).map(|_| (0..3).map(|_| { let v = (rnd() % n as u64) as i32 + 1; if rnd() % 2 == 0 { v } else { -v } }).collect()).collect();
            let row_holds = |row: &[Lit], m: &[bool]| row.iter().all(|l| m[l.var as usize] != l.neg);
            let holds = |m: &[bool]| boxes.iter().all(|rows| rows.iter().any(|r| row_holds(r, m))) && check_model(&cls, m);
            let brute = (0..1u32 << n).any(|bits| holds(&(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let tables: Vec<TableBox> = boxes.iter().map(|rows| TableBox::new(rows.clone())).collect();
            let mut solver: cadical::Solver = cadical::Solver::new();
            solver.reserve(n as i32);
            for c in &cls { solver.add_clause(c.iter().copied()); }
            let prop = BoxPropagator::new(tables);
            let observed = prop.observed_vars();
            solver.connect_propagator(Box::new(prop));
            for v in observed { solver.add_observed_var(v); }
            match solver.solve() {
                Some(true) => {
                    let m: Vec<bool> = (1..=n as i32).map(|v| solver.value(v).unwrap_or(true)).collect();
                    assert!(brute, "trial {trial}: cadical+boxes SAT, brute UNSAT: {boxes:?} {cls:?}");
                    assert!(holds(&m), "trial {trial}: bad model {m:?} for {boxes:?} {cls:?}");
                }
                Some(false) => assert!(!brute, "trial {trial}: cadical+boxes UNSAT, brute SAT: {boxes:?} {cls:?}"),
                None => panic!("no budget set"),
            }
        }
    }
}
