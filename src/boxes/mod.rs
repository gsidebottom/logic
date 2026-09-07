//! Box-matrix engine — M1a: DPLL over box rows with table propagation.
//!
//! Design: `doc/box_backend_design.md` §3.  The matrix is a set of **table
//! boxes**.  A row is a canonical partial assignment, stored here in *model*
//! polarity (the literals the row makes TRUE); the design doc's path-literal
//! polarity is the complement, and the two are interchanged only at the
//! boundary with the matrix-path enumerator.  A CNF clause is the smallest
//! table box — one single-literal row per literal — so a plain CNF becomes a
//! matrix of clause boxes and the engine is a complete SAT procedure; a
//! compiled box (an adder, …) is a table with more rows over more variables.
//!
//! Search (§3.2): pick a row of the most constrained undecided box, assign its
//! literals, propagate (§3.3: a box with no live row is a covered path →
//! backtrack; a literal shared by every live row is forced), repeat until
//! every box has a satisfied row (SAT, the assignment is a model) or the row
//! choices are exhausted (UNSAT).  Per-box row bitsets make "rows still live
//! after adding a literal" one AND and "is this literal forced" one subset
//! test, exactly the lifted form of unit propagation / generalized arc
//! consistency.

use crate::matrix::Lit;

/// Bitset over the rows of one box.
pub type RowMask = Vec<u64>;

fn mask_new(n: usize) -> RowMask { vec![0; (n + 63) / 64] }
fn mask_set(m: &mut RowMask, i: usize) { m[i / 64] |= 1u64 << (i % 64); }
fn mask_and_not(a: &RowMask, b: &RowMask) -> RowMask {
    a.iter().zip(b).map(|(x, y)| x & !y).collect()
}
fn mask_is_zero(a: &RowMask) -> bool { a.iter().all(|&w| w == 0) }
fn mask_count(a: &RowMask) -> usize { a.iter().map(|w| w.count_ones() as usize).sum() }
/// `a ⊆ b`
fn mask_subset(a: &RowMask, b: &RowMask) -> bool { a.iter().zip(b).all(|(x, y)| x & !y == 0) }
fn mask_ones(a: &RowMask) -> Vec<usize> {
    let mut out = Vec::new();
    for (wi, &w) in a.iter().enumerate() {
        let mut w = w;
        while w != 0 {
            let t = w.trailing_zeros() as usize;
            out.push(wi * 64 + t);
            w &= w - 1;
        }
    }
    out
}

/// A table box: canonical rows over a set of (0-based) variables, plus the
/// per-literal row masks that make propagation bit-parallel.
#[derive(Clone, Debug)]
pub struct TableBox {
    /// Sorted, distinct 0-based variables this box mentions.
    pub vars: Vec<u32>,
    /// Rows in model polarity; each sorted by variable, no duplicate or
    /// contradictory literals (such rows are dropped at construction).
    pub rows: Vec<Vec<Lit>>,
    /// Per local variable index: rows where that variable is TRUE / FALSE.
    mask_pos: Vec<RowMask>,
    mask_neg: Vec<RowMask>,
}

impl TableBox {
    /// Build a box from rows (0-based `Lit.var`).  Rows are canonicalized:
    /// literals sorted and deduplicated, rows containing a complementary
    /// pair dropped (they can never be chosen), duplicate rows merged.
    pub fn new(rows: Vec<Vec<Lit>>) -> TableBox {
        let mut canon: Vec<Vec<Lit>> = Vec::with_capacity(rows.len());
        'rows: for mut r in rows {
            r.sort_by_key(|l| (l.var, l.neg));
            r.dedup_by(|a, b| a.var == b.var && a.neg == b.neg);
            for w in r.windows(2) {
                if w[0].var == w[1].var { continue 'rows; }   // x and ¬x: unsatisfiable row
            }
            canon.push(r);
        }
        canon.sort_by(|a, b| a.iter().map(|l| (l.var, l.neg)).cmp(b.iter().map(|l| (l.var, l.neg))));
        canon.dedup();
        let mut vars: Vec<u32> = canon.iter().flatten().map(|l| l.var).collect();
        vars.sort_unstable();
        vars.dedup();
        let n = canon.len();
        let mut mask_pos = vec![mask_new(n); vars.len()];
        let mut mask_neg = vec![mask_new(n); vars.len()];
        for (ri, row) in canon.iter().enumerate() {
            for l in row {
                let li = vars.binary_search(&l.var).unwrap();
                if l.neg { mask_set(&mut mask_neg[li], ri) } else { mask_set(&mut mask_pos[li], ri) }
            }
        }
        TableBox { vars, rows: canon, mask_pos, mask_neg }
    }

    /// The smallest box: a CNF clause in DIMACS form (1-based, sign = polarity).
    pub fn clause(lits: &[i32]) -> TableBox {
        TableBox::new(lits.iter().map(|&l| vec![lit_of_dimacs(l)]).collect())
    }

    pub fn all_mask(&self) -> RowMask {
        let mut m = mask_new(self.rows.len());
        for i in 0..self.rows.len() { mask_set(&mut m, i) }
        m
    }
}

/// DIMACS literal → 0-based `Lit`.
pub fn lit_of_dimacs(l: i32) -> Lit {
    Lit { var: l.unsigned_abs() - 1, neg: l < 0 }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Val { U, T, F }

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Verdict {
    /// A model, indexed by 0-based variable (unconstrained variables are false).
    Sat(Vec<bool>),
    Unsat,
    /// Decision budget exhausted.
    Unknown,
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
}

struct Frame {
    b: usize,
    rows: Vec<usize>,
    next: usize,
}

/// The engine: boxes, the current partial assignment with a trail, and the
/// per-box live-row masks with their undo log.
pub struct Engine {
    nvars: usize,
    boxes: Vec<TableBox>,
    /// var → (box index, local variable index) occurrences.
    occ: Vec<Vec<(usize, usize)>>,
    vals: Vec<Val>,
    trail: Vec<u32>,
    trail_lim: Vec<usize>,
    live: Vec<RowMask>,
    live_undo: Vec<(usize, RowMask)>,
    live_undo_lim: Vec<usize>,
    in_queue: Vec<bool>,
    pub stats: Stats,
    /// Optional decision budget; `solve` returns `Unknown` when exceeded.
    pub max_decisions: Option<u64>,
}

impl Engine {
    pub fn new(nvars: usize, boxes: Vec<TableBox>) -> Engine {
        let mut e = Engine {
            nvars, boxes: Vec::new(), occ: vec![Vec::new(); nvars],
            vals: vec![Val::U; nvars], trail: Vec::new(), trail_lim: Vec::new(),
            live: Vec::new(), live_undo: Vec::new(), live_undo_lim: Vec::new(),
            in_queue: Vec::new(), stats: Stats::default(), max_decisions: None,
        };
        for b in boxes { e.add_box(b) }
        e
    }

    /// Every clause becomes a clause box.
    pub fn from_cnf(nvars: usize, clauses: &[Vec<i32>]) -> Engine {
        Engine::new(nvars, clauses.iter().map(|c| TableBox::clause(c)).collect())
    }

    pub fn add_box(&mut self, b: TableBox) {
        let bi = self.boxes.len();
        for (li, &v) in b.vars.iter().enumerate() {
            let v = v as usize;
            if v >= self.nvars {
                self.nvars = v + 1;
                self.occ.resize(self.nvars, Vec::new());
                self.vals.resize(self.nvars, Val::U);
            }
            self.occ[v].push((bi, li));
        }
        self.live.push(b.all_mask());
        self.in_queue.push(false);
        self.boxes.push(b);
    }

    pub fn nvars(&self) -> usize { self.nvars }
    pub fn nboxes(&self) -> usize { self.boxes.len() }

    fn new_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        self.live_undo_lim.push(self.live_undo.len());
    }

    fn backtrack_level(&mut self) {
        let t = self.trail_lim.pop().expect("backtrack below level 0");
        while self.trail.len() > t {
            let v = self.trail.pop().unwrap();
            self.vals[v as usize] = Val::U;
        }
        let u = self.live_undo_lim.pop().unwrap();
        while self.live_undo.len() > u {
            let (b, prev) = self.live_undo.pop().unwrap();
            self.live[b] = prev;
        }
    }

    /// Assign `var := val`; narrows the live rows of every box containing
    /// `var` and records the touched boxes.  `false` if already assigned the
    /// opposite value.
    fn assign(&mut self, var: u32, val: Val, touched: &mut Vec<usize>) -> bool {
        let v = var as usize;
        match self.vals[v] {
            x if x == val => return true,
            Val::U => {}
            _ => return false,
        }
        self.vals[v] = val;
        self.trail.push(var);
        for &(b, li) in &self.occ[v] {
            let kill = if val == Val::T { &self.boxes[b].mask_neg[li] } else { &self.boxes[b].mask_pos[li] };
            let nl = mask_and_not(&self.live[b], kill);
            if nl != self.live[b] {
                let prev = std::mem::replace(&mut self.live[b], nl);
                self.live_undo.push((b, prev));
                if !self.in_queue[b] { self.in_queue[b] = true; touched.push(b); }
            }
        }
        true
    }

    /// Table propagation to fixpoint over the touched boxes.  `false` on a
    /// conflict (some box has no live row).
    fn propagate(&mut self, mut queue: Vec<usize>) -> bool {
        while let Some(b) = queue.pop() {
            self.in_queue[b] = false;
            if mask_is_zero(&self.live[b]) {
                self.stats.conflicts += 1;
                for &q in &queue { self.in_queue[q] = false; }
                return false;
            }
            for li in 0..self.boxes[b].vars.len() {
                let var = self.boxes[b].vars[li];
                if self.vals[var as usize] != Val::U { continue; }
                let forced = if mask_subset(&self.live[b], &self.boxes[b].mask_pos[li]) { Some(Val::T) }
                             else if mask_subset(&self.live[b], &self.boxes[b].mask_neg[li]) { Some(Val::F) }
                             else { None };
                if let Some(val) = forced {
                    self.stats.propagations += 1;
                    if !self.assign(var, val, &mut queue) {
                        self.stats.conflicts += 1;
                        for &q in &queue { self.in_queue[q] = false; }
                        return false;
                    }
                }
            }
        }
        true
    }

    fn row_satisfied(&self, b: usize, r: usize) -> bool {
        self.boxes[b].rows[r].iter().all(|l| {
            self.vals[l.var as usize] == if l.neg { Val::F } else { Val::T }
        })
    }

    fn satisfied(&self, b: usize) -> bool {
        mask_ones(&self.live[b]).into_iter().any(|r| self.row_satisfied(b, r))
    }

    /// The undecided box with the fewest live rows; `None` when every box is
    /// satisfied (the current assignment is a model).
    fn choose_box(&self) -> Option<usize> {
        let mut best: Option<(usize, usize)> = None;
        for b in 0..self.boxes.len() {
            if self.satisfied(b) { continue; }
            let c = mask_count(&self.live[b]);
            if best.map_or(true, |(_, bc)| c < bc) { best = Some((b, c)); }
            if c <= 1 { break; }
        }
        best.map(|(b, _)| b)
    }

    /// Choose row `r` of box `b` at a fresh decision level and propagate.
    fn try_row(&mut self, b: usize, r: usize) -> bool {
        self.new_level();
        self.stats.decisions += 1;
        let mut touched = Vec::new();
        let lits = self.boxes[b].rows[r].clone();
        for l in lits {
            if !self.assign(l.var, if l.neg { Val::F } else { Val::T }, &mut touched) {
                for &q in &touched { self.in_queue[q] = false; }
                self.stats.conflicts += 1;
                self.backtrack_level();
                return false;
            }
        }
        if self.propagate(touched) { true } else { self.backtrack_level(); false }
    }

    pub fn solve(&mut self) -> Verdict {
        let all: Vec<usize> = (0..self.boxes.len()).collect();
        for &b in &all { self.in_queue[b] = true; }
        if !self.propagate(all) { return Verdict::Unsat; }
        let mut stack: Vec<Frame> = Vec::new();
        loop {
            match self.choose_box() {
                None => return Verdict::Sat(self.vals.iter().map(|&v| v == Val::T).collect()),
                Some(b) => stack.push(Frame { b, rows: mask_ones(&self.live[b]), next: 0 }),
            }
            loop {
                if let Some(max) = self.max_decisions {
                    if self.stats.decisions >= max { return Verdict::Unknown; }
                }
                let Some(fr) = stack.last_mut() else { return Verdict::Unsat };
                if fr.next >= fr.rows.len() {
                    stack.pop();
                    if stack.is_empty() { return Verdict::Unsat; }
                    self.backtrack_level();          // undo the parent's current row
                    continue;
                }
                let (b, r) = (fr.b, fr.rows[fr.next]);
                fr.next += 1;
                if self.try_row(b, r) { break; }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn solve(nvars: usize, cls: &[Vec<i32>]) -> Verdict { Engine::from_cnf(nvars, cls).solve() }

    fn check_model(cls: &[Vec<i32>], m: &[bool]) -> bool {
        cls.iter().all(|c| c.iter().any(|&l| m[(l.unsigned_abs() - 1) as usize] == (l > 0)))
    }

    #[test]
    fn trivial() {
        assert_eq!(solve(1, &[vec![]]), Verdict::Unsat);
        assert_eq!(solve(1, &[vec![1]]), Verdict::Sat(vec![true]));
        assert_eq!(solve(1, &[vec![1], vec![-1]]), Verdict::Unsat);
        assert_eq!(solve(2, &[vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]]), Verdict::Unsat);
    }

    /// Pigeonhole: p pigeons, h holes; var (i,j) = pigeon i in hole j.
    fn php(p: usize, h: usize) -> (usize, Vec<Vec<i32>>) {
        let v = |i: usize, j: usize| (i * h + j + 1) as i32;
        let mut cls = Vec::new();
        for i in 0..p { cls.push((0..h).map(|j| v(i, j)).collect()); }
        for j in 0..h { for a in 0..p { for b in a + 1..p { cls.push(vec![-v(a, j), -v(b, j)]); } } }
        (p * h, cls)
    }

    #[test]
    fn pigeonhole() {
        let (n, c) = php(3, 2); assert_eq!(solve(n, &c), Verdict::Unsat);
        let (n, c) = php(4, 3); assert_eq!(solve(n, &c), Verdict::Unsat);
        let (n, c) = php(3, 3); match solve(n, &c) { Verdict::Sat(m) => assert!(check_model(&c, &m)), v => panic!("{v:?}") }
    }

    /// Random 3-SAT against brute force.
    #[test]
    fn random_vs_bruteforce() {
        let mut seed: u64 = 0x9E3779B97F4A7C15;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for trial in 0..300 {
            let n = 3 + (rnd() % 6) as usize;
            let m = 2 + (rnd() % (4 * n as u64)) as usize;
            let cls: Vec<Vec<i32>> = (0..m).map(|_| {
                (0..3).map(|_| { let v = (rnd() % n as u64) as i32 + 1; if rnd() % 2 == 0 { v } else { -v } }).collect()
            }).collect();
            let brute = (0..1u32 << n).any(|bits| {
                let m: Vec<bool> = (0..n).map(|i| bits >> i & 1 == 1).collect();
                check_model(&cls, &m)
            });
            match solve(n, &cls) {
                Verdict::Sat(model) => { assert!(brute, "trial {trial}: engine SAT, brute UNSAT"); assert!(check_model(&cls, &model), "trial {trial}: bad model"); }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT: {cls:?}"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
    }

    /// The full-adder table from doc/box_backend_design.md §1 (model polarity),
    /// vars X=0 Y=1 C1=2 Z=3 C=4 U1=5 U2=6 U3=7.
    fn adder_box() -> TableBox {
        let table = [
            [0,0,0, 0,0, 0,0,0], [0,0,1, 1,0, 0,0,0], [0,1,0, 1,0, 0,0,1], [0,1,1, 0,1, 0,1,1],
            [1,0,0, 1,0, 0,0,1], [1,0,1, 0,1, 0,1,1], [1,1,0, 0,1, 1,0,0], [1,1,1, 1,1, 1,0,0],
        ];
        TableBox::new(table.iter().map(|row| {
            row.iter().enumerate().map(|(v, &bit)| Lit { var: v as u32, neg: bit == 0 }).collect()
        }).collect())
    }

    #[test]
    fn compiled_adder_box() {
        let adder = adder_box();
        assert_eq!(adder.rows.len(), 8);
        // X=1, Y=1, C1=0  ⇒  Z=0, C=1 (and U1=1, U2=0, U3=0), by propagation alone
        let mut e = Engine::new(8, vec![adder.clone(), TableBox::clause(&[1]), TableBox::clause(&[2]), TableBox::clause(&[-3])]);
        match e.solve() {
            Verdict::Sat(m) => { assert_eq!(&m[..8], &[true, true, false, false, true, true, false, false]); assert_eq!(e.stats.decisions, 0, "inputs fixed ⇒ no decisions needed"); }
            v => panic!("{v:?}"),
        }
        // same inputs but demand C=0: UNSAT
        let mut e = Engine::new(8, vec![adder.clone(), TableBox::clause(&[1]), TableBox::clause(&[2]), TableBox::clause(&[-3]), TableBox::clause(&[-5])]);
        assert_eq!(e.solve(), Verdict::Unsat);
        // free inputs: SAT, and every model is a table row
        let mut e = Engine::new(8, vec![adder.clone()]);
        match e.solve() { Verdict::Sat(m) => { let row: Vec<Lit> = (0..8).map(|v| Lit { var: v, neg: !m[v as usize] }).collect(); assert!(adder.rows.contains(&row)); } v => panic!("{v:?}") }
    }
}

pub mod compile;
pub mod expand;
