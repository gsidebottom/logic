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
//! Propagation (§3.3): a box with no live row is a covered path → conflict;
//! a literal shared by every live row is forced.  Per-box row bitsets make
//! "rows still live after adding a literal" one AND and "is this literal
//! forced" one subset test, exactly the lifted form of unit propagation /
//! generalized arc consistency.  Search (§3.2, §3.5): conflict-driven —
//! conflicts and forced literals are explained from the kill masks, learned
//! clauses are propagated with watched literals.  A box may also be given in
//! **clause form** (the negated rows of its negation): the same constraint,
//! cheaper to propagate when the tables are tiny.

use crate::matrix::Lit;

/// Bitset over the rows of one box.
pub type RowMask = Vec<u64>;

fn mask_set(m: &mut RowMask, i: usize) { m[i / 64] |= 1u64 << (i % 64); }
fn mask_and_not(a: &RowMask, b: &RowMask) -> RowMask {
    a.iter().zip(b).map(|(x, y)| x & !y).collect()
}
fn mask_is_zero(a: &RowMask) -> bool { a.iter().all(|&w| w == 0) }
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
    /// Flat kill masks: the rows that die when local variable `li` is
    /// assigned FALSE (`mask_pos`, at `(2·li)·nwords`) or TRUE (`mask_neg`,
    /// at `(2·li + 1)·nwords`) — one contiguous array per box.
    kill: Vec<u64>,
    /// Words in a row mask (at least one, so an empty box has a zero word).
    nwords: usize,
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
        let nwords = n.div_ceil(64).max(1);
        let mut mask_pos = vec![vec![0u64; nwords]; vars.len()];
        let mut mask_neg = vec![vec![0u64; nwords]; vars.len()];
        for (ri, row) in canon.iter().enumerate() {
            for l in row {
                let li = vars.binary_search(&l.var).unwrap();
                if l.neg { mask_set(&mut mask_neg[li], ri) } else { mask_set(&mut mask_pos[li], ri) }
            }
        }
        let mut kill = Vec::with_capacity(2 * vars.len() * nwords);
        for li in 0..vars.len() { kill.extend_from_slice(&mask_pos[li]); kill.extend_from_slice(&mask_neg[li]); }
        TableBox { vars, rows: canon, mask_pos, mask_neg, kill, nwords }
    }


    /// The smallest box: a CNF clause in DIMACS form (1-based, sign = polarity).
    pub fn clause(lits: &[i32]) -> TableBox {
        TableBox::new(lits.iter().map(|&l| vec![lit_of_dimacs(l)]).collect())
    }

    /// Does some row survive the partial assignment `value_of` (true = the
    /// variable is TRUE)?  A row dies when it needs the opposite value.
    pub fn has_live_row(&self, value_of: &dyn Fn(u32) -> Option<bool>) -> bool {
        let mut live = self.all_mask();
        for (i, &v) in self.vars.iter().enumerate() {
            if let Some(b) = value_of(v) {
                live = mask_and_not(&live, if b { &self.mask_neg[i] } else { &self.mask_pos[i] });
                if mask_is_zero(&live) { return false; }
            }
        }
        !mask_is_zero(&live)
    }

    pub fn all_mask(&self) -> RowMask {
        let mut m = vec![0u64; self.nwords];
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

/// Where a box's data lives in the engine's flat arrays.
#[derive(Clone, Copy)]
struct BoxHdr {
    /// First word of the box's live mask in `live`.
    off: u32,
    /// Words per row mask.
    nw: u32,
    /// The box's variables: `vars_all[vbase .. vbase + nvars]`.
    vbase: u32,
    nvars: u32,
    /// Kill masks: local variable `li` assigned FALSE kills the rows in
    /// `kill_all[kbase + 2·li·nw ..]`, TRUE those at `kbase + (2·li + 1)·nw`.
    kbase: u32,
    nrows: u32,
}

/// One occurrence of a variable: the box and the start of the variable's
/// FALSE-kill mask in `kill_all` (the TRUE-kill mask follows it).
#[derive(Clone, Copy)]
struct Occ { b: u32, koff: u32 }

/// Why a variable holds its value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Reason { None, Box(u32), Clause(u32) }

/// What propagation ran into.
#[derive(Clone, Copy, Debug)]
enum Conflict {
    /// The clause is false.
    Clause(u32),
    /// The box has no live row.
    Box(u32),
    /// The box forces `var := val`, which is already assigned the other way.
    Forced { b: u32, var: u32, val: bool },
}

/// Growth of the learned-clause budget after each reduction.
const REDUCE_STEP: usize = 300;

#[inline] fn code(var: u32, neg: bool) -> u32 { var << 1 | neg as u32 }
/// The value of literal code `c` under `vals`.
#[inline] fn lit_val(vals: &[Val], c: u32) -> Val {
    match vals[(c >> 1) as usize] { Val::U => Val::U, v => if (v == Val::T) != (c & 1 == 1) { Val::T } else { Val::F } }
}

/// The engine: conflict-driven search (§3.2, §3.5) over two kinds of
/// constraint — **table boxes**, propagated to generalized arc consistency
/// with bit-parallel live-row masks, and **clauses** (a box's clause form,
/// and the clauses learned from conflicts), propagated with two watched
/// literals.
///
/// A conflict, or a literal a table forces, is explained lazily from the
/// table's kill masks: the assigned literals of the box whose kill masks
/// together cover the rows that had to die (fewest, oldest levels first).
/// With that, 1-UIP conflict analysis, backjumping, learned clauses, VSIDS
/// branching with phase saving and Luby restarts are the textbook ones.
///
/// The hot path is allocation-free: every box's data sits in flat arrays
/// indexed through a small header; an assignment ANDs the killed rows out of
/// each live word; opening a decision level snapshots the whole live array
/// (a few hundred words) and backjumping copies one back.
pub struct Engine {
    nvars: usize,
    // tables
    hdr: Vec<BoxHdr>,
    vars_all: Vec<u32>,
    kill_all: Vec<u64>,
    /// var → occurrences in tables.
    occ: Vec<Vec<Occ>>,
    /// Live-row masks, box `b` at words `hdr[b].off ..`.
    live: Vec<u64>,
    /// Snapshots of `live` at the start of each open decision level.
    snap: Vec<u64>,
    in_queue: Vec<bool>,
    queue: Vec<u32>,
    // clauses
    clauses: Vec<Vec<u32>>,
    /// Per literal code: the clauses watching it (visited when it becomes
    /// FALSE), each with a blocker literal.
    watches: Vec<Vec<(u32, u32)>>,
    /// Clauses `[first_learnt..]` were learned.
    first_learnt: usize,
    /// Per learned clause (index − first_learnt): literal block distance and
    /// activity; a deleted clause keeps its slot (watches drop it lazily).
    learnt_lbd: Vec<u32>,
    learnt_act: Vec<f64>,
    deleted: Vec<bool>,
    cla_inc: f64,
    /// Conflicts until the next reduction of the learned clauses.
    reduce_at: u64,
    /// Learned clauses kept before the first reduction (grows by
    /// `REDUCE_STEP` each time); a test may lower it.
    pub reduce_start: usize,
    unsat_at_init: bool,
    // assignment
    vals: Vec<Val>,
    level: Vec<u32>,
    reason: Vec<Reason>,
    trail_pos: Vec<u32>,
    trail: Vec<u32>,
    trail_lim: Vec<usize>,
    qhead: usize,
    // heuristic
    activity: Vec<f64>,
    var_inc: f64,
    phase: Vec<bool>,
    seen: Vec<bool>,
    pub stats: Stats,
    /// Optional decision budget; `solve` returns `Unknown` when exceeded.
    pub max_decisions: Option<u64>,
    /// Cooperative cancellation: checked every 256 decisions; `solve` returns `Unknown`.
    pub cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
}

impl Engine {
    pub fn new(nvars: usize, boxes: Vec<TableBox>) -> Engine {
        let mut e = Engine {
            nvars: 0, hdr: Vec::new(), vars_all: Vec::new(), kill_all: Vec::new(), occ: Vec::new(), live: Vec::new(), snap: Vec::new(), in_queue: Vec::new(), queue: Vec::new(),
            clauses: Vec::new(), watches: Vec::new(), first_learnt: 0,
            learnt_lbd: Vec::new(), learnt_act: Vec::new(), deleted: Vec::new(), cla_inc: 1.0, reduce_at: 0, reduce_start: 4000,
            unsat_at_init: false,
            vals: Vec::new(), level: Vec::new(), reason: Vec::new(), trail_pos: Vec::new(),
            trail: Vec::new(), trail_lim: Vec::new(), qhead: 0,
            activity: Vec::new(), var_inc: 1.0, phase: Vec::new(), seen: Vec::new(),
            stats: Stats::default(), max_decisions: None, cancel: None,
        };
        e.grow(nvars);
        for b in boxes { e.add_box(b) }
        e
    }

    /// Every clause becomes a watched clause.
    pub fn from_cnf(nvars: usize, clauses: &[Vec<i32>]) -> Engine {
        let mut e = Engine::new(nvars, Vec::new());
        for c in clauses { e.add_clause(&c.iter().map(|&l| lit_of_dimacs(l)).collect::<Vec<_>>()); }
        e
    }

    fn grow(&mut self, nvars: usize) {
        if nvars <= self.nvars { return; }
        self.nvars = nvars;
        self.occ.resize(nvars, Vec::new());
        self.vals.resize(nvars, Val::U);
        self.level.resize(nvars, 0);
        self.reason.resize(nvars, Reason::None);
        self.trail_pos.resize(nvars, 0);
        self.activity.resize(nvars, 0.0);
        self.phase.resize(nvars, false);
        self.seen.resize(nvars, false);
        self.watches.resize(2 * nvars, Vec::new());
    }

    /// Add a table box (before solving).
    pub fn add_box(&mut self, b: TableBox) {
        let bi = self.hdr.len() as u32;
        let nw = b.nwords as u32;
        let (vbase, kbase) = (self.vars_all.len() as u32, self.kill_all.len() as u32);
        if let Some(&max) = b.vars.iter().max() { self.grow(max as usize + 1); }
        for (li, &v) in b.vars.iter().enumerate() {
            self.occ[v as usize].push(Occ { b: bi, koff: kbase + 2 * li as u32 * nw });
        }
        self.vars_all.extend_from_slice(&b.vars);
        self.kill_all.extend_from_slice(&b.kill);
        let off = self.live.len();
        self.hdr.push(BoxHdr { off: off as u32, nw, vbase, nvars: b.vars.len() as u32, kbase, nrows: b.rows.len() as u32 });
        self.live.extend_from_slice(&b.all_mask());
        // Rows already killed by the level-0 assignment (a unit clause added
        // before the box, say): `live` must always reflect the whole trail,
        // or the table looks alive when it is dead and its conflict surfaces
        // levels later with no literal of the current level.
        debug_assert!(self.decision_level() == 0, "boxes are added before solving");
        let nw = nw as usize;
        for (li, &v) in b.vars.iter().enumerate() {
            let val = self.vals[v as usize];
            if val == Val::U { continue; }
            let kb = kbase as usize + 2 * li * nw + if val == Val::T { nw } else { 0 };
            for w in 0..nw { self.live[off + w] &= !self.kill_all[kb + w]; }
        }
        self.in_queue.push(false);
    }

    /// Add a clause (before solving).  Tautologies are dropped, duplicate
    /// literals merged; the empty clause makes the engine unsatisfiable, a
    /// unit clause is a level-0 assignment.
    pub fn add_clause(&mut self, lits: &[Lit]) {
        if let Some(max) = lits.iter().map(|l| l.var).max() { self.grow(max as usize + 1); }
        let mut c: Vec<u32> = lits.iter().map(|l| code(l.var, l.neg)).collect();
        c.sort_unstable(); c.dedup();
        if c.windows(2).any(|w| w[0] >> 1 == w[1] >> 1) { return; }   // x ∨ ¬x
        match c.len() {
            0 => self.unsat_at_init = true,
            1 => { let l = c[0]; if !self.assign(l >> 1, if l & 1 == 1 { Val::F } else { Val::T }, Reason::None) { self.unsat_at_init = true; } }
            _ => {
                let ci = self.clauses.len() as u32;
                self.watches[c[0] as usize].push((ci, c[1]));
                self.watches[c[1] as usize].push((ci, c[0]));
                self.clauses.push(c);
                self.deleted.push(false);
                self.first_learnt = self.clauses.len();
            }
        }
    }

    pub fn nvars(&self) -> usize { self.nvars }
    pub fn nboxes(&self) -> usize { self.hdr.len() }
    pub fn nclauses(&self) -> usize { self.clauses.len() }
    fn decision_level(&self) -> usize { self.trail_lim.len() }

    #[inline] fn lit_value(&self, c: u32) -> Val { lit_val(&self.vals, c) }

    fn new_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        self.snap.extend_from_slice(&self.live);
    }

    /// Undo decision levels above `lvl`.
    fn backjump(&mut self, lvl: usize) {
        if self.decision_level() <= lvl { return; }
        let t = self.trail_lim[lvl];
        while self.trail.len() > t {
            let v = self.trail.pop().unwrap() as usize;
            self.phase[v] = self.vals[v] == Val::T;
            self.vals[v] = Val::U;
            self.reason[v] = Reason::None;
        }
        let n = self.live.len();
        let start = self.trail_lim.len() - lvl;   // levels popped
        let from = self.snap.len() - start * n;
        self.live.copy_from_slice(&self.snap[from..from + n]);
        self.snap.truncate(from);
        self.trail_lim.truncate(lvl);
        self.qhead = self.trail.len();
        self.clear_queue();
    }

    fn clear_queue(&mut self) {
        for &q in &self.queue { self.in_queue[q as usize] = false; }
        self.queue.clear();
    }

    /// Assign `var := val`: narrow the live rows of every box containing
    /// `var`, queueing the box for propagation when they changed.  `false`
    /// if already assigned the opposite value.
    fn assign(&mut self, var: u32, val: Val, reason: Reason) -> bool {
        let v = var as usize;
        match self.vals[v] {
            x if x == val => return true,
            Val::U => {}
            _ => return false,
        }
        self.vals[v] = val;
        self.level[v] = self.decision_level() as u32;
        self.reason[v] = reason;
        self.trail_pos[v] = self.trail.len() as u32;
        self.trail.push(var);
        for k in 0..self.occ[v].len() {
            let Occ { b, koff } = self.occ[v][k];
            let h = self.hdr[b as usize];
            let (off, nw) = (h.off as usize, h.nw as usize);
            let kb = koff as usize + if val == Val::T { nw } else { 0 };
            let mut changed = false;
            for w in 0..nw {
                let old = self.live[off + w];
                let new = old & !self.kill_all[kb + w];
                if new != old { self.live[off + w] = new; changed = true; }
            }
            if changed && !self.in_queue[b as usize] { self.in_queue[b as usize] = true; self.queue.push(b); }
        }
        true
    }

    /// Propagate to fixpoint: clauses through the trail (two watched
    /// literals), tables through the queue of boxes whose live rows shrank.
    fn propagate(&mut self) -> Option<Conflict> {
        loop {
            while self.qhead < self.trail.len() {
                let v = self.trail[self.qhead];
                self.qhead += 1;
                let false_lit = code(v, self.vals[v as usize] == Val::T);   // the literal made FALSE
                let mut ws = std::mem::take(&mut self.watches[false_lit as usize]);
                let mut i = 0;
                let mut j = 0;
                let mut conflict = None;
                while i < ws.len() {
                    let (ci, blocker) = ws[i];
                    i += 1;
                    if self.deleted[ci as usize] { continue; }
                    if self.lit_value(blocker) == Val::T { ws[j] = (ci, blocker); j += 1; continue; }
                    let c = &mut self.clauses[ci as usize];
                    if c[0] == false_lit { c.swap(0, 1); }
                    let other = c[0];
                    if other != blocker && lit_val(&self.vals, other) == Val::T { ws[j] = (ci, other); j += 1; continue; }
                    // a new watch: any literal not false
                    let mut found = false;
                    for k in 2..c.len() {
                        if lit_val(&self.vals, c[k]) != Val::F {
                            c.swap(1, k);
                            let w = c[1];
                            self.watches[w as usize].push((ci, other));
                            found = true;
                            break;
                        }
                    }
                    if found { continue; }
                    ws[j] = (ci, other); j += 1;
                    if self.lit_value(other) == Val::F {
                        conflict = Some(Conflict::Clause(ci));
                        while i < ws.len() { ws[j] = ws[i]; i += 1; j += 1; }
                        break;
                    }
                    self.stats.propagations += 1;
                    self.assign(other >> 1, if other & 1 == 1 { Val::F } else { Val::T }, Reason::Clause(ci));
                }
                ws.truncate(j);
                self.watches[false_lit as usize] = ws;
                if let Some(c) = conflict { self.clear_queue(); return Some(c); }
            }
            let b = self.queue.pop()?;
            let b = b as usize;
            self.in_queue[b] = false;
            let h = self.hdr[b];
            let (off, nw) = (h.off as usize, h.nw as usize);
            if (0..nw).all(|w| self.live[off + w] == 0) { self.clear_queue(); return Some(Conflict::Box(b as u32)); }
            for li in 0..h.nvars as usize {
                let var = self.vars_all[h.vbase as usize + li];
                if self.vals[var as usize] != Val::U { continue; }
                // every live row has var TRUE ⇔ assigning FALSE would kill them all
                let kf = h.kbase as usize + 2 * li * nw;
                let kt = kf + nw;
                let forced = if (0..nw).all(|w| self.live[off + w] & !self.kill_all[kf + w] == 0) { Some(Val::T) }
                             else if (0..nw).all(|w| self.live[off + w] & !self.kill_all[kt + w] == 0) { Some(Val::F) }
                             else { None };
                if let Some(val) = forced {
                    self.stats.propagations += 1;
                    if !self.assign(var, val, Reason::Box(b as u32)) {
                        self.clear_queue();
                        return Some(Conflict::Forced { b: b as u32, var, val: val == Val::T });
                    }
                }
            }
        }
    }

    /// The literals (all FALSE now) explaining why the rows in `target` of
    /// box `b` are dead: assigned variables of the box, oldest levels first,
    /// whose kill masks cover `target`; only assignments before trail
    /// position `before` count.
    fn explain_box(&self, b: u32, target: &mut [u64], before: usize, out: &mut Vec<u32>) {
        let h = self.hdr[b as usize];
        let nw = h.nw as usize;
        let mut cands: Vec<(u32, u32, usize)> = (0..h.nvars as usize)
            .map(|li| (self.vars_all[h.vbase as usize + li], li))
            .filter(|&(v, _)| self.vals[v as usize] != Val::U && (self.trail_pos[v as usize] as usize) < before)
            .map(|(v, li)| (self.level[v as usize], self.trail_pos[v as usize], li)).collect();
        cands.sort_unstable();
        for (_, _, li) in cands {
            if target.iter().all(|&w| w == 0) { break; }
            let var = self.vars_all[h.vbase as usize + li];
            let val = self.vals[var as usize];
            let kb = h.kbase as usize + 2 * li * nw + if val == Val::T { nw } else { 0 };
            let mut hit = false;
            for (w, t) in target.iter_mut().enumerate().take(nw) {
                let x = *t & self.kill_all[kb + w];
                if x != 0 { *t &= !x; hit = true; }
            }
            if hit { out.push(code(var, val == Val::T)); }   // the false literal ¬(var = val)
        }
        debug_assert!(target.iter().all(|&w| w == 0), "explanation does not cover the dead rows");
    }

    /// The rows of box `b` (all of them, or those not having `var = val`).
    fn rows_mask(&self, b: u32, except: Option<(usize, bool)>) -> Vec<u64> {
        let h = self.hdr[b as usize];
        let nw = h.nw as usize;
        let mut m = vec![0u64; nw];
        for r in 0..h.nrows as usize { m[r / 64] |= 1 << (r % 64); }
        if let Some((li, val)) = except {
            // rows having var = val: the rows killed by the opposite value
            let kb = h.kbase as usize + 2 * li * nw + if val { 0 } else { nw };
            for (w, mw) in m.iter_mut().enumerate() { *mw &= !self.kill_all[kb + w]; }
        }
        m
    }

    fn local_index(&self, b: u32, var: u32) -> usize {
        let h = self.hdr[b as usize];
        let s = h.vbase as usize;
        self.vars_all[s..s + h.nvars as usize].binary_search(&var).expect("variable not in box")
    }

    /// The false literals of the reason for `var`'s value (its own literal excluded).
    fn reason_lits(&self, var: u32, out: &mut Vec<u32>) {
        match self.reason[var as usize] {
            Reason::None => {}
            Reason::Clause(ci) => for &l in &self.clauses[ci as usize] { if l >> 1 != var { out.push(l); } },
            Reason::Box(b) => {
                let li = self.local_index(b, var);
                let val = self.vals[var as usize] == Val::T;
                let mut target = self.rows_mask(b, Some((li, val)));
                self.explain_box(b, &mut target, self.trail_pos[var as usize] as usize, out);
            }
        }
    }

    /// The false literals of a conflict.
    fn conflict_lits(&self, conflict: Conflict, out: &mut Vec<u32>) {
        match conflict {
            Conflict::Clause(ci) => out.extend_from_slice(&self.clauses[ci as usize]),
            Conflict::Box(b) => { let mut target = self.rows_mask(b, None); self.explain_box(b, &mut target, self.trail.len(), out); }
            Conflict::Forced { b, var, val } => {
                let li = self.local_index(b, var);
                let mut target = self.rows_mask(b, Some((li, val)));
                self.explain_box(b, &mut target, self.trail.len(), out);
                out.push(code(var, !val));   // "var = val" — false, since var holds the other value
            }
        }
    }

    fn bump_clause(&mut self, ci: u32) {
        let Some(k) = (ci as usize).checked_sub(self.first_learnt) else { return };
        self.learnt_act[k] += self.cla_inc;
        if self.learnt_act[k] > 1e20 {
            for a in &mut self.learnt_act { *a *= 1e-20; }
            self.cla_inc *= 1e-20;
        }
    }

    /// The literal block distance of a clause: its literals' distinct levels.
    fn lbd(&self, c: &[u32]) -> u32 {
        let mut levels: Vec<u32> = c.iter().map(|&l| self.level[(l >> 1) as usize]).collect();
        levels.sort_unstable(); levels.dedup();
        levels.len() as u32
    }

    /// Delete the less useful half of the learned clauses — glue clauses
    /// (LBD ≤ 2) and current reasons are kept; the rest go by LBD, then
    /// activity.  Watches drop deleted clauses lazily.
    fn reduce_db(&mut self) {
        let n = self.clauses.len() - self.first_learnt;
        let mut order: Vec<usize> = (0..n).filter(|&k| !self.deleted[self.first_learnt + k]).collect();
        order.sort_by(|&a, &b| self.learnt_lbd[b].cmp(&self.learnt_lbd[a])
            .then(self.learnt_act[a].partial_cmp(&self.learnt_act[b]).unwrap_or(std::cmp::Ordering::Equal)));
        let mut removed = 0usize;
        for &k in order.iter().take(order.len() / 2) {
            if self.learnt_lbd[k] <= 2 { continue; }
            let ci = self.first_learnt + k;
            // a clause that is the reason for its first literal stays
            let l0 = self.clauses[ci][0];
            if self.reason[(l0 >> 1) as usize] == Reason::Clause(ci as u32) && self.vals[(l0 >> 1) as usize] != Val::U { continue; }
            self.deleted[ci] = true;
            self.clauses[ci] = Vec::new();
            removed += 1;
        }
        let _ = removed;
    }

    fn bump(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity { *a *= 1e-100; }
            self.var_inc *= 1e-100;
        }
    }

    /// 1-UIP conflict analysis of a conflict given by its (false) literals,
    /// at least one of them at the current level: the learned clause
    /// (asserting literal first) and the level to backjump to.
    fn analyze(&mut self, mut lits: Vec<u32>) -> (Vec<u32>, usize) {
        let current = self.decision_level() as u32;
        let mut learnt: Vec<u32> = vec![0];
        let mut path = 0usize;
        let mut idx = self.trail.len();
        loop {
            for &q in &lits {
                let v = (q >> 1) as usize;
                if self.seen[v] || self.level[v] == 0 { continue; }
                self.seen[v] = true;
                self.bump(v);
                if self.level[v] == current { path += 1; } else { learnt.push(q); }
            }
            // the next seen variable down the trail
            loop { idx -= 1; if self.seen[self.trail[idx] as usize] { break; } }
            let v = self.trail[idx];
            self.seen[v as usize] = false;
            path -= 1;
            if path == 0 {
                learnt[0] = code(v, self.vals[v as usize] == Val::T);   // the UIP's false literal
                break;
            }
            if let Reason::Clause(ci) = self.reason[v as usize] { self.bump_clause(ci); }
            lits.clear();
            self.reason_lits(v, &mut lits);
        }
        for &q in &learnt[1..] { self.seen[(q >> 1) as usize] = false; }
        // backjump level: the highest level among the other literals (moved to position 1)
        let mut bj = 0usize;
        if learnt.len() > 1 {
            let mut best = 1;
            for i in 1..learnt.len() { if self.level[(learnt[i] >> 1) as usize] > self.level[(learnt[best] >> 1) as usize] { best = i; } }
            learnt.swap(1, best);
            bj = self.level[(learnt[1] >> 1) as usize] as usize;
        }
        (learnt, bj)
    }

    /// Level-0 propagation of every box and clause.  `false` if they alone conflict.
    pub fn init(&mut self) -> bool {
        if self.unsat_at_init { return false; }
        self.clear_queue();
        for b in 0..self.hdr.len() { self.in_queue[b] = true; self.queue.push(b as u32); }
        self.qhead = 0;
        if self.propagate().is_some() { self.unsat_at_init = true; return false; }
        true
    }

    /// Solve under extra unit assumptions, leaving the engine as it was: one
    /// engine serves many queries (the box-aware path search checks every
    /// completed path this way instead of rebuilding an engine per path).
    /// Each assumption is a decision at its own level, so the clauses learned
    /// meanwhile hold without them and are kept.  Assumes [`init`](Self::init) was run.
    pub fn solve_under(&mut self, units: &[Lit]) -> Verdict {
        if self.unsat_at_init { return Verdict::Unsat; }
        let base = self.decision_level();
        let v = self.search(base, units);
        self.backjump(base);
        v
    }

    pub fn solve(&mut self) -> Verdict {
        if !self.init() { return Verdict::Unsat; }
        self.solve_under(&[])
    }

    /// The Luby sequence (1, 1, 2, 1, 1, 2, 4, …).
    fn luby(mut i: u64) -> u64 {
        let (mut size, mut seq) = (1u64, 0u32);
        while size < i + 1 { seq += 1; size = 2 * size + 1; }
        while size - 1 != i { size = (size - 1) >> 1; seq -= 1; i %= size; }
        1u64 << seq
    }

    /// Conflict-driven search above level `base`, deciding `assumptions`
    /// first (each at its own level).
    fn search(&mut self, base: usize, assumptions: &[Lit]) -> Verdict {
        let mut restarts = 0u64;
        let mut conflicts_here = 0u64;
        loop {
            if let Some(conflict) = self.propagate() {
                self.stats.conflicts += 1;
                conflicts_here += 1;
                let mut lits = Vec::new();
                self.conflict_lits(conflict, &mut lits);
                // A conflict whose literals all lie below the current level
                // is a conflict at the highest of their levels: analysis
                // starts there (it cannot happen while `live` tracks the
                // trail, but a conflict with no current-level literal would
                // otherwise walk off the trail).
                let top = lits.iter().map(|&q| self.level[(q >> 1) as usize] as usize).max().unwrap_or(0);
                if top < self.decision_level() { self.backjump(top.max(base)); }
                if self.decision_level() <= base { return Verdict::Unsat; }
                if self.stats.conflicts & 255 == 0 && let Some(c) = &self.cancel && c.load(std::sync::atomic::Ordering::Relaxed) { return Verdict::Unknown; }
                let (learnt, bj) = self.analyze(lits);
                self.backjump(bj.max(base));
                let l0 = learnt[0];
                if learnt.len() == 1 {
                    self.assign(l0 >> 1, if l0 & 1 == 1 { Val::F } else { Val::T }, Reason::None);
                } else {
                    let ci = self.clauses.len() as u32;
                    self.watches[learnt[0] as usize].push((ci, learnt[1]));
                    self.watches[learnt[1] as usize].push((ci, learnt[0]));
                    let lbd = self.lbd(&learnt);
                    self.clauses.push(learnt);
                    self.deleted.push(false);
                    self.learnt_lbd.push(lbd);
                    self.learnt_act.push(self.cla_inc);
                    self.assign(l0 >> 1, if l0 & 1 == 1 { Val::F } else { Val::T }, Reason::Clause(ci));
                }
                self.var_inc *= 1.0 / 0.95;
                self.cla_inc *= 1.0 / 0.999;
                if self.reduce_at == 0 { self.reduce_at = self.stats.conflicts + self.reduce_start as u64; }
                if self.stats.conflicts >= self.reduce_at {
                    self.reduce_db();
                    self.reduce_start += REDUCE_STEP;
                    self.reduce_at = self.stats.conflicts + self.reduce_start as u64;
                }
                if conflicts_here >= 64 * Self::luby(restarts) {
                    restarts += 1; conflicts_here = 0;
                    self.backjump(base);
                }
                continue;
            }
            if let Some(max) = self.max_decisions && self.stats.decisions >= max { return Verdict::Unknown; }
            if self.stats.decisions & 255 == 0 && let Some(c) = &self.cancel && c.load(std::sync::atomic::Ordering::Relaxed) { return Verdict::Unknown; }
            // assumptions first, one level each
            let lvl = self.decision_level();
            if lvl < base + assumptions.len() {
                let a = &assumptions[lvl - base];
                let want = if a.neg { Val::F } else { Val::T };
                match self.vals[a.var as usize] {
                    x if x == want => { self.new_level(); }
                    Val::U => { self.new_level(); self.assign(a.var, want, Reason::None); }
                    _ => return Verdict::Unsat,
                }
                continue;
            }
            // VSIDS decision
            let mut best: Option<usize> = None;
            for v in 0..self.nvars {
                if self.vals[v] == Val::U && best.is_none_or(|b| self.activity[v] > self.activity[b]) { best = Some(v); }
            }
            let Some(v) = best else { return Verdict::Sat(self.vals.iter().map(|&x| x == Val::T).collect()) };
            self.new_level();
            self.stats.decisions += 1;
            self.assign(v as u32, if self.phase[v] { Val::T } else { Val::F }, Reason::None);
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

    /// Random table boxes (and some clauses) against brute force: exercises
    /// table propagation, lazy explanations and learning together.
    #[test]
    fn random_tables_vs_bruteforce() {
        let mut seed: u64 = 0x1234_5678_9ABC_DEF1;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        for trial in 0..400 {
            let n = 3 + (rnd() % 6) as usize;
            let nboxes = 1 + (rnd() % 5) as usize;
            let mut boxes: Vec<Vec<Vec<Lit>>> = Vec::new();
            for _ in 0..nboxes {
                let k = 2 + (rnd() % 3) as usize;                 // columns
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
            let row_holds = |row: &[Lit], m: &[bool]| row.iter().all(|l| m[l.var as usize] == !l.neg);
            let holds = |m: &[bool]| boxes.iter().all(|rows| rows.iter().any(|r| row_holds(r, m))) && check_model(&cls, m);
            let brute = (0..1u32 << n).any(|bits| holds(&(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let mut e = Engine::new(n, boxes.iter().map(|rows| TableBox::new(rows.clone())).collect());
            for c in &cls { e.add_clause(&c.iter().map(|&l| lit_of_dimacs(l)).collect::<Vec<_>>()); }
            match e.solve() {
                Verdict::Sat(m) => { assert!(brute, "trial {trial}: engine SAT, brute UNSAT"); assert!(holds(&m), "trial {trial}: bad model"); }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT: {boxes:?} {cls:?}"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
    }

    /// Tables added after the clauses — after unit clauses in particular,
    /// which assign at level 0 before the tables exist (the `sat -b boxes
    /// --boxes` order): the new table's live rows must reflect those
    /// assignments.  Checked against brute force.
    #[test]
    fn tables_after_units_vs_bruteforce() {
        let mut seed: u64 = 0x0DDB_1A5E_5BAD_5EED;
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
            // clauses of 1..3 literals: units assign at level 0 during `from_cnf`
            let nclauses = 1 + (rnd() % 4) as usize;
            let mut cls: Vec<Vec<i32>> = Vec::new();
            for _ in 0..nclauses {
                let len = 1 + (rnd() % 3) as usize;
                let mut c = Vec::new();
                for _ in 0..len { let v = (rnd() % n as u64) as i32 + 1; c.push(if rnd() % 2 == 0 { v } else { -v }); }
                cls.push(c);
            }
            let row_holds = |row: &[Lit], m: &[bool]| row.iter().all(|l| m[l.var as usize] == !l.neg);
            let holds = |m: &[bool]| boxes.iter().all(|rows| rows.iter().any(|r| row_holds(r, m))) && check_model(&cls, m);
            let brute = (0..1u32 << n).any(|bits| holds(&(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let mut e = Engine::from_cnf(n, &cls);
            for rows in &boxes { e.add_box(TableBox::new(rows.clone())); }
            match e.solve() {
                Verdict::Sat(m) => { assert!(brute, "trial {trial}: engine SAT, brute UNSAT"); assert!(holds(&m), "trial {trial}: bad model"); }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT: {cls:?} {boxes:?}"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
    }

    /// Learned-clause deletion is exercised (a low `reduce_start`) on random
    /// 3-SAT near the threshold, checked against brute force.
    #[test]
    fn deletion_keeps_answers() {
        let mut seed: u64 = 0xC0FFEE_1234_5678;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let (n, m) = (16usize, 76usize);   // ratio 4.75: mostly UNSAT, hundreds of conflicts
        let mut deletions_seen = false;
        for trial in 0..12 {
            let cls: Vec<Vec<i32>> = (0..m).map(|_| {
                let mut c = Vec::new();
                while c.len() < 3 { let v = (rnd() % n as u64) as i32 + 1; if !c.iter().any(|&x: &i32| x.abs() == v) { c.push(if rnd() % 2 == 0 { v } else { -v }); } }
                c
            }).collect();
            let brute = (0..1u32 << n).any(|bits| check_model(&cls, &(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let mut e = Engine::from_cnf(n, &cls);
            e.reduce_start = 8;
            let v = e.solve();
            let ndel = e.deleted.iter().filter(|&&d| d).count();
            eprintln!("trial {trial}: {} conflicts, {} learned, {ndel} deleted", e.stats.conflicts, e.clauses.len() - e.first_learnt);
            deletions_seen |= ndel > 0;
            match v {
                Verdict::Sat(model) => { assert!(brute, "trial {trial}: engine SAT, brute UNSAT"); assert!(check_model(&cls, &model), "trial {trial}: bad model"); }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
        assert!(deletions_seen, "the test never deleted a clause — lower reduce_start or raise m");
    }

    /// Solving under assumptions keeps the engine reusable, and the clauses
    /// learned under one set of assumptions stay valid for the next.
    #[test]
    fn assumptions_are_reusable() {
        // (a ∨ b) (¬a ∨ c) (¬b ∨ c): c is forced; under ¬c: UNSAT, under c: SAT, twice
        let mut e = Engine::from_cnf(3, &[vec![1, 2], vec![-1, 3], vec![-2, 3]]);
        assert!(e.init());
        let c = |var: u32, neg: bool| Lit { var, neg };
        assert_eq!(e.solve_under(&[c(2, true)]), Verdict::Unsat);
        assert!(matches!(e.solve_under(&[c(2, false)]), Verdict::Sat(_)));
        assert_eq!(e.solve_under(&[c(2, true), c(0, false)]), Verdict::Unsat);
        assert!(matches!(e.solve_under(&[c(0, false)]), Verdict::Sat(m) if m[0] && m[2]));
        assert!(matches!(e.solve_under(&[]), Verdict::Sat(_)));
    }

    /// w(4;4;n): every 4-term arithmetic progression in 1..n as an `ap4` box
    /// — the compiled minimal table of "not all equal": a cyclic cover
    /// {c=0 d=1}, {b=0 c=1}, {a=0 b=1}, {a=1 d=0}.
    fn waerden4(n: usize) -> (usize, Vec<TableBox>) {
        let lit = |v: usize, value: bool| Lit { var: v as u32 - 1, neg: !value };
        let mut boxes = Vec::new();
        for d in 1..=n {
            for i in 1..=n {
                if i + 3 * d > n { break; }
                let (a, b, c, e) = (i, i + d, i + 2 * d, i + 3 * d);
                boxes.push(TableBox::new(vec![
                    vec![lit(c, false), lit(e, true)], vec![lit(b, false), lit(c, true)],
                    vec![lit(a, false), lit(b, true)], vec![lit(a, true), lit(e, false)]]));
            }
        }
        (n, boxes)
    }

    /// Engine speed on van der Waerden: `cargo test --release --lib bench_waerden -- --ignored --nocapture`.
    #[test]
    #[ignore]
    fn bench_waerden() {
        let iters: usize = std::env::var("BENCH_ITERS").ok().and_then(|s| s.parse().ok()).unwrap_or(5);
        for form in ["tables", "clauses"] {
            for n in [35usize, 34] {
                let (nv, boxes) = waerden4(n);
                let mut best = std::time::Duration::MAX;
                let mut stats = Stats::default();
                let mut verdict = "?";
                for _ in 0..iters {
                    let mut e = if form == "tables" { Engine::new(nv, boxes.clone()) } else {
                        // the two clauses of each progression: not all 0, not all 1
                        let mut e = Engine::new(nv, Vec::new());
                        for b in &boxes {
                            e.add_clause(&b.vars.iter().map(|&v| Lit { var: v, neg: false }).collect::<Vec<_>>());
                            e.add_clause(&b.vars.iter().map(|&v| Lit { var: v, neg: true }).collect::<Vec<_>>());
                        }
                        e
                    };
                    let t0 = std::time::Instant::now();
                    let v = e.solve();
                    best = best.min(t0.elapsed());
                    stats = e.stats.clone();
                    verdict = match v { Verdict::Sat(_) => "SAT", Verdict::Unsat => "UNSAT", Verdict::Unknown => "?" };
                }
                eprintln!("w(4;4;{n}) as {form}: {verdict} best of {iters}: {best:?}; {stats:?}");
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
pub mod controller;
