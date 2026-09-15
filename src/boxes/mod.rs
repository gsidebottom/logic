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
    /// Table explanations computed (conflicts and reasons), the literals
    /// they contained, and the literals minimisation dropped.
    pub explanations: u64,
    pub explanation_lits: u64,
    pub explanation_dropped: u64,
    /// Reason explanations served from the per-assignment cache.
    pub explanation_hits: u64,
    /// Learned clauses, and their literals before and after minimisation.
    pub learned: u64,
    pub learned_lits_raw: u64,
    pub learned_lits: u64,
    /// Learned clauses deleted by the reductions, and reductions run.
    pub deleted: u64,
    pub reductions: u64,
    pub restarts: u64,
    /// Variables eliminated by `simplify`, and its clause counts before and after.
    pub eliminated: u64,
    pub clauses_before: u64,
    pub clauses_after: u64,
    /// Inprocessing rounds, variables eliminated in them, learned clauses
    /// vivified (shortened) and the literals they lost; rephases.
    pub inprocess_rounds: u64,
    pub inprocess_eliminated: u64,
    pub vivified: u64,
    pub vivified_lits: u64,
    pub rephases: u64,
}

/// How a table's explanation is chosen among the assigned literals whose
/// kill masks cover the rows that had to die (`BOXES_EXPLAIN` selects it).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum ExplainMode {
    /// Trail order, oldest levels first, every literal that kills a row
    /// not yet covered — not minimal (the baseline before minimisation).
    Greedy,
    /// The same pass, preferring level-0 and already-seen literals, then
    /// made inclusion-minimal: newest pick first, a literal the others
    /// cover for is dropped (a minimal hitting set of the rows' killers).
    Minimal,
    /// Largest remaining coverage first (set-cover greedy, ties by the same
    /// preference), then made inclusion-minimal — the shortest explanations
    /// of the three and the default (§10.1 of the design doc: 2.2 literals
    /// against greedy's 4.9 on the pyhala-braun cones, 3.9× faster).
    #[default]
    Cover,
}

/// Restart policy (`BOXES_RESTART` selects it).
#[derive(Clone, Copy, PartialEq, Eq, Debug, Default)]
pub enum RestartMode {
    /// Luby sequence, unit 64 conflicts.
    Luby,
    /// Glucose's dynamic restarts — the last 50 learned clauses' LBD against
    /// the running average, blocked while the trail is long — alternating
    /// with stable phases of Luby restarts (unit 512) whose length doubles;
    /// on a restart the trail is reused down to the first decision the
    /// heap would now make differently.
    #[default]
    Glucose,
}

impl RestartMode {
    /// `BOXES_RESTART=luby|glucose`, default `glucose`.
    pub fn from_env() -> RestartMode {
        match std::env::var("BOXES_RESTART").as_deref() { Ok("luby") => RestartMode::Luby, _ => RestartMode::Glucose }
    }
}

impl ExplainMode {
    /// `BOXES_EXPLAIN=greedy|minimal|cover`, default `cover`.
    pub fn from_env() -> ExplainMode {
        match std::env::var("BOXES_EXPLAIN").as_deref() {
            Ok("greedy") => ExplainMode::Greedy,
            Ok("minimal") => ExplainMode::Minimal,
            _ => ExplainMode::Cover,
        }
    }
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
    /// Decision order: a binary max-heap on activity (ties to the lower
    /// variable) holding every unassigned variable, and some assigned ones
    /// dropped lazily when popped.
    heap: Vec<u32>,
    /// Variable → position in `heap`, `u32::MAX` when absent.
    heap_pos: Vec<u32>,
    /// Recursive minimisation of learned clauses (`BOXES_MINIMIZE`).
    pub minimize: bool,
    min_stack: Vec<u32>,
    min_clear: Vec<u32>,
    min_lits: Vec<u32>,
    /// A table-propagated variable's explanation, computed once per
    /// assignment (`expl_ok`) and reused by every analysis until the
    /// variable is unassigned.
    expl_cache: Vec<Vec<u32>>,
    expl_ok: Vec<bool>,
    /// Restart policy and its state (see `RestartMode`).
    pub restart: RestartMode,
    lbd_q: std::collections::VecDeque<u32>,
    lbd_q_sum: u64,
    lbd_sum: u64,
    trail_q: std::collections::VecDeque<u32>,
    trail_q_sum: u64,
    stable: bool,
    stable_len: u64,
    stable_toggle_at: u64,
    /// Variables `simplify` resolved away (never decided) and, per
    /// elimination in order, the clauses removed with it — replayed
    /// backwards to extend a model.
    eliminated: Vec<bool>,
    elim: Vec<(u32, Vec<Vec<u32>>)>,
    /// Elimination may run during the search (set by `simplify`: no
    /// variable of this engine is ever assumed).
    elim_enabled: bool,
    /// Target and best phases (`BOXES_PHASES=1`, off by default: §10.1 of
    /// the design doc): the assignment of the longest trail since the last
    /// restart, used in stable mode, and of the longest ever, used by
    /// rephasing.
    pub phases: bool,
    target_phase: Vec<bool>,
    target_size: usize,
    best_phase: Vec<bool>,
    best_size: usize,
    rephase_at: u64,
    rephase_count: u64,
    rng: u64,
    /// Inprocessing (`BOXES_INPROCESS=1`, off by default: §10.1 of the
    /// design doc): every `inprocess_interval` conflicts, at level 0,
    /// re-eliminate and vivify.
    pub inprocess: bool,
    inprocess_at: u64,
    inprocess_interval: u64,
    pub stats: Stats,
    /// Optional decision budget; `solve` returns `Unknown` when exceeded.
    pub max_decisions: Option<u64>,
    /// Cooperative cancellation: checked every 256 decisions; `solve` returns `Unknown`.
    pub cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    /// How table explanations are chosen.
    pub explain: ExplainMode,
    // scratch for `explain_box`: (class, level, trail position, local index, kill-mask base)
    expl_cands: Vec<(u8, u32, u32, u32, u32)>,
    expl_orig: Vec<u64>,
    expl_picked: Vec<(u32, u32, u8)>,
    expl_keep: Vec<bool>,
    expl_used: Vec<bool>,
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
            heap: Vec::new(), heap_pos: Vec::new(),
            minimize: !matches!(std::env::var("BOXES_MINIMIZE").as_deref(), Ok("0") | Ok("none") | Ok("off")),
            min_stack: Vec::new(), min_clear: Vec::new(), min_lits: Vec::new(),
            expl_cache: Vec::new(), expl_ok: Vec::new(),
            restart: RestartMode::from_env(),
            lbd_q: std::collections::VecDeque::new(), lbd_q_sum: 0, lbd_sum: 0,
            trail_q: std::collections::VecDeque::new(), trail_q_sum: 0,
            stable: false, stable_len: 1000, stable_toggle_at: 1000,
            eliminated: Vec::new(), elim: Vec::new(), elim_enabled: false,
            phases: matches!(std::env::var("BOXES_PHASES").as_deref(), Ok("1") | Ok("on")),
            target_phase: Vec::new(), target_size: 0, best_phase: Vec::new(), best_size: 0,
            rephase_at: 1000, rephase_count: 0, rng: 0x9E37_79B9_7F4A_7C15,
            inprocess: matches!(std::env::var("BOXES_INPROCESS").as_deref(), Ok("1") | Ok("on")),
            inprocess_at: 10_000, inprocess_interval: 10_000,
            stats: Stats::default(), max_decisions: None, cancel: None,
            explain: ExplainMode::from_env(),
            expl_cands: Vec::new(), expl_orig: Vec::new(), expl_picked: Vec::new(), expl_keep: Vec::new(), expl_used: Vec::new(),
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
        self.expl_cache.resize_with(nvars, Vec::new);
        self.expl_ok.resize(nvars, false);
        self.eliminated.resize(nvars, false);
        self.target_phase.resize(nvars, false);
        self.best_phase.resize(nvars, false);
        let old = self.heap_pos.len();
        self.heap_pos.resize(nvars, u32::MAX);
        for v in old..nvars { self.heap_insert(v as u32); }
    }

    // --- the decision heap ---

    /// `a` before `b`: higher activity, then the lower variable (the order the
    /// linear scan it replaces had).
    #[inline] fn heap_before(&self, a: u32, b: u32) -> bool {
        let (x, y) = (self.activity[a as usize], self.activity[b as usize]);
        x > y || (x == y && a < b)
    }

    fn heap_up(&mut self, mut i: usize) {
        let v = self.heap[i];
        while i > 0 {
            let p = (i - 1) / 2;
            let u = self.heap[p];
            if !self.heap_before(v, u) { break; }
            self.heap[i] = u; self.heap_pos[u as usize] = i as u32;
            i = p;
        }
        self.heap[i] = v; self.heap_pos[v as usize] = i as u32;
    }

    fn heap_down(&mut self, mut i: usize) {
        let v = self.heap[i];
        let n = self.heap.len();
        loop {
            let l = 2 * i + 1;
            if l >= n { break; }
            let r = l + 1;
            let c = if r < n && self.heap_before(self.heap[r], self.heap[l]) { r } else { l };
            let u = self.heap[c];
            if !self.heap_before(u, v) { break; }
            self.heap[i] = u; self.heap_pos[u as usize] = i as u32;
            i = c;
        }
        self.heap[i] = v; self.heap_pos[v as usize] = i as u32;
    }

    fn heap_insert(&mut self, v: u32) {
        if self.heap_pos[v as usize] != u32::MAX { return; }
        self.heap_pos[v as usize] = self.heap.len() as u32;
        self.heap.push(v);
        self.heap_up(self.heap.len() - 1);
    }

    /// The most active unassigned variable, left in the heap (assigned or
    /// eliminated ones above it are dropped).
    fn heap_peek_unassigned(&mut self) -> Option<u32> {
        while let Some(&v) = self.heap.first() {
            if self.vals[v as usize] == Val::U && !self.eliminated[v as usize] { return Some(v); }
            self.heap_pop();
        }
        None
    }

    /// The variable of highest activity in the heap (assigned or not).
    fn heap_pop(&mut self) -> Option<u32> {
        let top = *self.heap.first()?;
        let last = self.heap.pop().unwrap();
        self.heap_pos[top as usize] = u32::MAX;
        if !self.heap.is_empty() {
            self.heap[0] = last; self.heap_pos[last as usize] = 0;
            self.heap_down(0);
        }
        Some(top)
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
            self.expl_ok[v] = false;
            self.heap_insert(v as u32);
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
    /// box `b` are dead: assigned variables of the box whose kill masks
    /// cover `target`; only assignments before trail position `before`
    /// count.  Which cover, per `self.explain`: the greedy trail-order one
    /// (oldest levels first), or an inclusion-minimal one — a minimal
    /// hitting set of the rows' killers — preferring literals that cost a
    /// learned clause nothing (level 0, or already seen by the analysis).
    fn explain_box(&mut self, b: u32, target: &mut [u64], before: usize, out: &mut Vec<u32>) {
        let h = self.hdr[b as usize];
        let nw = h.nw as usize;
        let mode = self.explain;
        let mut cands = std::mem::take(&mut self.expl_cands);
        cands.clear();
        for li in 0..h.nvars as usize {
            let v = self.vars_all[h.vbase as usize + li] as usize;
            let val = self.vals[v];
            if val == Val::U || self.trail_pos[v] as usize >= before { continue; }
            // `Greedy` is the plain trail order (the baseline); the others
            // put the free literals first
            let class = if mode == ExplainMode::Greedy { 2 } else if self.level[v] == 0 { 0 } else if self.seen[v] { 1 } else { 2 };
            let kb = h.kbase as usize + 2 * li * nw + if val == Val::T { nw } else { 0 };
            cands.push((class, self.level[v], self.trail_pos[v], li as u32, kb as u32));
        }
        cands.sort_unstable();
        let mut orig = std::mem::take(&mut self.expl_orig);
        orig.clear();
        orig.extend_from_slice(&target[..nw]);
        let mut picked = std::mem::take(&mut self.expl_picked);
        picked.clear();
        let mut used = std::mem::take(&mut self.expl_used);
        match mode {
            ExplainMode::Greedy | ExplainMode::Minimal => {
                for &(class, _, _, li, kb) in &cands {
                    if target[..nw].iter().all(|&w| w == 0) { break; }
                    let kb = kb as usize;
                    let mut hit = false;
                    for w in 0..nw {
                        let x = target[w] & self.kill_all[kb + w];
                        if x != 0 { target[w] &= !x; hit = true; }
                    }
                    if hit { picked.push((li, kb as u32, class)); }
                }
            }
            ExplainMode::Cover => {
                used.clear();
                used.resize(cands.len(), false);
                while target[..nw].iter().any(|&w| w != 0) {
                    let mut best: Option<(u32, usize)> = None;
                    for (ci, &(_, _, _, _, kb)) in cands.iter().enumerate() {
                        if used[ci] { continue; }
                        let kb = kb as usize;
                        let cnt: u32 = (0..nw).map(|w| (target[w] & self.kill_all[kb + w]).count_ones()).sum();
                        if cnt > 0 && best.is_none_or(|(c, _)| cnt > c) { best = Some((cnt, ci)); }
                    }
                    let Some((_, ci)) = best else { break };
                    used[ci] = true;
                    let (class, _, _, li, kb) = cands[ci];
                    for w in 0..nw { target[w] &= !self.kill_all[kb as usize + w]; }
                    picked.push((li, kb, class));
                }
            }
        }
        debug_assert!(target[..nw].iter().all(|&w| w == 0), "explanation does not cover the dead rows");
        let mut keep = std::mem::take(&mut self.expl_keep);
        keep.clear();
        keep.resize(picked.len(), true);
        if mode != ExplainMode::Greedy && picked.len() > 1 {
            // inclusion-minimal: newest pick first, drop a literal the kept
            // others cover for (free literals — level 0, seen — stay)
            for i in (0..picked.len()).rev() {
                if picked[i].2 < 2 { continue; }
                let mut covered = true;
                for w in 0..nw {
                    let mut c = 0u64;
                    for (j, p) in picked.iter().enumerate() { if j != i && keep[j] { c |= self.kill_all[p.1 as usize + w]; } }
                    if c & orig[w] != orig[w] { covered = false; break; }
                }
                if covered { keep[i] = false; self.stats.explanation_dropped += 1; }
            }
        }
        self.stats.explanations += 1;
        for (i, &(li, _, _)) in picked.iter().enumerate() {
            if !keep[i] { continue; }
            let var = self.vars_all[h.vbase as usize + li as usize];
            out.push(code(var, self.vals[var as usize] == Val::T));   // the false literal ¬(var = val)
            self.stats.explanation_lits += 1;
        }
        self.expl_cands = cands;
        self.expl_orig = orig;
        self.expl_picked = picked;
        self.expl_keep = keep;
        self.expl_used = used;
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
    fn reason_lits(&mut self, var: u32, out: &mut Vec<u32>) {
        match self.reason[var as usize] {
            Reason::None => {}
            Reason::Clause(ci) => for &l in &self.clauses[ci as usize] { if l >> 1 != var { out.push(l); } },
            Reason::Box(b) => {
                if self.expl_ok[var as usize] {
                    self.stats.explanation_hits += 1;
                    out.extend_from_slice(&self.expl_cache[var as usize]);
                    return;
                }
                let li = self.local_index(b, var);
                let val = self.vals[var as usize] == Val::T;
                let mut target = self.rows_mask(b, Some((li, val)));
                let start = out.len();
                self.explain_box(b, &mut target, self.trail_pos[var as usize] as usize, out);
                let mut cache = std::mem::take(&mut self.expl_cache[var as usize]);
                cache.clear();
                cache.extend_from_slice(&out[start..]);
                self.expl_cache[var as usize] = cache;
                self.expl_ok[var as usize] = true;
            }
        }
    }

    /// The false literals of a conflict.
    fn conflict_lits(&mut self, conflict: Conflict, out: &mut Vec<u32>) {
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
        self.stats.deleted += removed as u64;
        self.stats.reductions += 1;
    }

    fn bump(&mut self, v: usize) {
        self.activity[v] += self.var_inc;
        if self.activity[v] > 1e100 {
            for a in &mut self.activity { *a *= 1e-100; }   // order preserved: the heap stands
            self.var_inc *= 1e-100;
        }
        let i = self.heap_pos[v];
        if i != u32::MAX { self.heap_up(i as usize); }
    }

    /// MiniSat's recursive test: the false literal of `v` is redundant in
    /// the learned clause when its reason's literals are all in the clause
    /// (seen) or level 0 or themselves redundant.  `levels` is the clause's
    /// abstract level set; a reason literal outside it ends the search.
    fn lit_redundant(&mut self, v: u32, levels: u32) -> bool {
        let top = self.min_clear.len();
        self.min_stack.clear();
        self.min_stack.push(v);
        while let Some(p) = self.min_stack.pop() {
            let mut lits = std::mem::take(&mut self.min_lits);
            lits.clear();
            self.reason_lits(p, &mut lits);
            let mut ok = true;
            for &q in &lits {
                let u = (q >> 1) as usize;
                if self.seen[u] || self.level[u] == 0 { continue; }
                if self.reason[u] != Reason::None && (1u32 << (self.level[u] & 31)) & levels != 0 {
                    self.seen[u] = true;
                    self.min_stack.push(u as u32);
                    self.min_clear.push(u as u32);
                } else { ok = false; break; }
            }
            self.min_lits = lits;
            if !ok {
                for &x in &self.min_clear[top..] { self.seen[x as usize] = false; }
                self.min_clear.truncate(top);
                return false;
            }
        }
        true
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
        self.stats.learned += 1;
        self.stats.learned_lits_raw += learnt.len() as u64;
        if self.minimize && learnt.len() > 2 {
            let levels = learnt[1..].iter().fold(0u32, |m, &q| m | 1 << (self.level[(q >> 1) as usize] & 31));
            // every variable marked seen — the clause's own (dropped ones included)
            // and those the redundancy search marks — is cleared at the end
            self.min_clear.clear();
            self.min_clear.extend(learnt[1..].iter().map(|&q| q >> 1));
            let mut j = 1;
            for i in 1..learnt.len() {
                let v = learnt[i] >> 1;
                if self.reason[v as usize] == Reason::None || !self.lit_redundant(v, levels) { learnt[j] = learnt[i]; j += 1; }
            }
            learnt.truncate(j);
            for k in 0..self.min_clear.len() { let x = self.min_clear[k]; self.seen[x as usize] = false; }
        }
        self.stats.learned_lits += learnt.len() as u64;
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
        debug_assert!(units.iter().all(|u| !self.eliminated[u.var as usize]), "an eliminated variable cannot be assumed");
        let base = self.decision_level();
        let v = self.search(base, units);
        self.backjump(base);
        match v {
            Verdict::Sat(mut m) => { self.reconstruct(&mut m); Verdict::Sat(m) }
            v => v,
        }
    }

    /// Extend a model over the surviving variables to the eliminated ones:
    /// last eliminated first, each takes the value satisfying every clause
    /// removed with it (TRUE if some removed clause with the positive
    /// literal has no other true literal, else FALSE).
    fn reconstruct(&self, m: &mut [bool]) {
        let holds = |m: &[bool], l: u32| m[(l >> 1) as usize] == (l & 1 == 0);
        for (v, clauses) in self.elim.iter().rev() {
            let v = *v as usize;
            let pos = code(v as u32, false);
            m[v] = clauses.iter().any(|c| c.contains(&pos) && !c.iter().any(|&l| (l >> 1) as usize != v && holds(m, l)));
        }
    }

    /// Bounded variable elimination on the clauses (SatELite): after the
    /// level-0 propagation, a variable in no table and still unassigned is
    /// resolved away when its resolvents (tautologies dropped, at most 20
    /// literals) are no more than the clauses they replace; the removed
    /// clauses are kept for `reconstruct`.  Two passes, cheapest variables
    /// first.  `false` if the formula is found unsatisfiable.
    pub fn simplify(&mut self) -> bool {
        debug_assert!(self.decision_level() == 0, "simplify runs before the search");
        if !self.init() { return false; }
        self.elim_enabled = true;
        self.eliminate_round();
        if self.unsat_at_init { return false; }
        self.init()
    }

    /// One elimination round at level 0 over the original clauses under
    /// the current assignment; learned clauses that mention an eliminated
    /// variable are dropped, the rest survive the rebuild.
    fn eliminate_round(&mut self) {
        let n = self.nvars;
        // the original clauses under the level-0 assignment
        let mut cls: Vec<Vec<u32>> = Vec::new();
        for ci in 0..self.first_learnt {
            if self.deleted[ci] || self.clauses[ci].iter().any(|&l| self.lit_value(l) == Val::T) { continue; }
            let c: Vec<u32> = self.clauses[ci].iter().copied().filter(|&l| self.lit_value(l) != Val::F).collect();
            debug_assert!(c.len() >= 2, "level-0 propagation left a unit or empty clause");
            cls.push(c);
        }
        let learned: Vec<(Vec<u32>, u32, f64)> = (self.first_learnt..self.clauses.len())
            .filter(|&ci| !self.deleted[ci] && !self.clauses[ci].iter().any(|&l| self.lit_value(l) == Val::T))
            .map(|ci| (self.clauses[ci].iter().copied().filter(|&l| self.lit_value(l) != Val::F).collect(), self.learnt_lbd[ci - self.first_learnt], self.learnt_act[ci - self.first_learnt]))
            .collect();
        self.stats.clauses_before = cls.len() as u64;
        let mut alive = vec![true; cls.len()];
        let mut occ: Vec<Vec<usize>> = vec![Vec::new(); 2 * n];
        for (i, c) in cls.iter().enumerate() { for &l in c { occ[l as usize].push(i); } }
        let frozen: Vec<bool> = (0..n).map(|v| !self.occ[v].is_empty() || self.vals[v] != Val::U).collect();
        let resolve = |a: &[u32], b: &[u32], v: usize| -> Option<Vec<u32>> {
            let mut r: Vec<u32> = a.iter().chain(b.iter()).copied().filter(|&l| (l >> 1) as usize != v).collect();
            r.sort_unstable(); r.dedup();
            if r.windows(2).any(|w| w[0] >> 1 == w[1] >> 1) { return None; }   // tautology
            Some(r)
        };
        for _pass in 0..2 {
            let mut order: Vec<usize> = (0..n).filter(|&v| !frozen[v] && !self.eliminated[v]).collect();
            order.retain(|&v| occ[2 * v].iter().any(|&i| alive[i]) || occ[2 * v + 1].iter().any(|&i| alive[i]));
            order.sort_by_key(|&v| occ[2 * v].len() * occ[2 * v + 1].len());
            for v in order {
                let pos: Vec<usize> = occ[2 * v].iter().copied().filter(|&i| alive[i]).collect();
                let neg: Vec<usize> = occ[2 * v + 1].iter().copied().filter(|&i| alive[i]).collect();
                if pos.len() > 16 || neg.len() > 16 { continue; }
                let mut resolvents: Vec<Vec<u32>> = Vec::new();
                let mut ok = true;
                'outer: for &i in &pos {
                    for &j in &neg {
                        if let Some(r) = resolve(&cls[i], &cls[j], v) {
                            if r.len() > 20 || resolvents.len() >= pos.len() + neg.len() { ok = false; break 'outer; }
                            resolvents.push(r);
                        }
                    }
                }
                if !ok { continue; }
                let removed: Vec<Vec<u32>> = pos.iter().chain(neg.iter()).map(|&i| { alive[i] = false; std::mem::take(&mut cls[i]) }).collect();
                self.elim.push((v as u32, removed));
                self.eliminated[v] = true;
                self.stats.eliminated += 1;
                for r in resolvents {
                    let idx = cls.len();
                    for &l in &r { occ[l as usize].push(idx); }
                    cls.push(r); alive.push(true);
                }
            }
        }
        // rebuild the clause store: the surviving originals, then the
        // learned clauses free of eliminated variables
        self.clauses.clear(); self.deleted.clear(); self.learnt_lbd.clear(); self.learnt_act.clear();
        self.first_learnt = 0;
        for w in &mut self.watches { w.clear(); }
        for v in 0..n { if self.vals[v] != Val::U { self.reason[v] = Reason::None; } }   // level-0 reasons pointed into the old store
        let mut kept = 0u64;
        for (i, c) in cls.iter().enumerate() {
            if !alive[i] { continue; }
            kept += 1;
            let lits: Vec<Lit> = c.iter().map(|&l| Lit { var: l >> 1, neg: l & 1 == 1 }).collect();
            self.add_clause(&lits);
        }
        self.stats.clauses_after = kept;
        for (c, lbd, act) in learned {
            if c.iter().any(|&l| self.eliminated[(l >> 1) as usize]) { continue; }
            self.add_learned(c, lbd, act);
        }
        self.qhead = 0;
    }

    pub fn solve(&mut self) -> Verdict {
        if !self.init() { return Verdict::Unsat; }
        self.solve_under(&[])
    }

    /// Whether to restart after a conflict that learned a clause of LBD
    /// `lbd` with `trail_len` literals assigned when it happened;
    /// `conflicts_here` / `restarts` count since this search began.
    fn restart_due(&mut self, lbd: u32, trail_len: u32, conflicts_here: u64, restarts: u64) -> bool {
        match self.restart {
            RestartMode::Luby => conflicts_here >= 64 * Self::luby(restarts),
            RestartMode::Glucose => {
                if self.stats.conflicts >= self.stable_toggle_at {
                    self.stable = !self.stable;
                    self.stable_len *= 2;
                    self.stable_toggle_at = self.stats.conflicts + self.stable_len;
                    self.lbd_q.clear(); self.lbd_q_sum = 0;
                }
                self.lbd_sum += lbd as u64;
                if self.lbd_q.len() == 50 { self.lbd_q_sum -= self.lbd_q.pop_front().unwrap() as u64; }
                self.lbd_q.push_back(lbd); self.lbd_q_sum += lbd as u64;
                if self.trail_q.len() == 5000 { self.trail_q_sum -= self.trail_q.pop_front().unwrap() as u64; }
                self.trail_q.push_back(trail_len); self.trail_q_sum += trail_len as u64;
                if self.stable { return conflicts_here >= 512 * Self::luby(restarts); }
                // blocking: a trail much longer than usual may be near a model
                if self.stats.conflicts > 10_000 && self.trail_q.len() == 5000 && trail_len as f64 > 1.4 * self.trail_q_sum as f64 / 5000.0 {
                    self.lbd_q.clear(); self.lbd_q_sum = 0;
                }
                if self.lbd_q.len() == 50 && self.lbd_q_sum as f64 / 50.0 * 0.8 > self.lbd_sum as f64 / self.stats.learned.max(1) as f64 {
                    self.lbd_q.clear(); self.lbd_q_sum = 0;
                    return true;
                }
                false
            }
        }
    }

    /// Restart: back to `base`, or — reusing the trail — to the last level
    /// whose decision still outranks the variable the heap would pick.
    fn restart(&mut self, base: usize) {
        self.stats.restarts += 1;
        self.target_size = 0;
        if self.phases && self.stats.conflicts >= self.rephase_at { self.rephase(); }
        let mut keep = base;
        if self.restart == RestartMode::Glucose && let Some(next) = self.heap_peek_unassigned() {
            while keep < self.decision_level() {
                let at = self.trail_lim[keep];
                if at >= self.trail.len() { break; }
                let d = self.trail[at];
                if self.heap_before(next, d) { break; }
                keep += 1;
            }
        }
        self.backjump(keep);
    }

    /// After a conflict-free propagation: a trail longer than any since
    /// the last restart becomes the target phases, longer than any ever
    /// the best phases.
    fn update_phases(&mut self) {
        let n = self.trail.len();
        if n > self.target_size {
            self.target_size = n;
            for &v in &self.trail { self.target_phase[v as usize] = self.vals[v as usize] == Val::T; }
        }
        if n > self.best_size {
            self.best_size = n;
            for &v in &self.trail { self.best_phase[v as usize] = self.vals[v as usize] == Val::T; }
        }
    }

    /// Reset the saved phases: best, original (false), best, inverted
    /// (true), best, random — in turn, at intervals growing by 1000.
    fn rephase(&mut self) {
        self.stats.rephases += 1;
        let k = self.rephase_count % 6;
        self.rephase_count += 1;
        self.rephase_at = self.stats.conflicts + 1000 * (self.rephase_count + 1);
        for v in 0..self.nvars {
            self.phase[v] = match k {
                0 | 2 | 4 => self.best_phase[v],
                1 => false,
                3 => true,
                _ => { self.rng ^= self.rng << 13; self.rng ^= self.rng >> 7; self.rng ^= self.rng << 17; self.rng & 1 == 1 }
            };
        }
        self.target_size = 0;
    }

    /// An inprocessing round at level 0: re-eliminate (when the engine's
    /// variables are never assumed) and vivify the kept learned clauses.
    fn inprocess_round(&mut self) {
        debug_assert!(self.decision_level() == 0);
        self.stats.inprocess_rounds += 1;
        if self.elim_enabled {
            let before = self.stats.eliminated;
            self.eliminate_round();
            self.stats.inprocess_eliminated += self.stats.eliminated - before;
            if self.unsat_at_init { return; }
            if self.propagate().is_some() { self.unsat_at_init = true; return; }
        }
        self.vivify();
    }

    /// Vivification (Luo et al.): for each kept learned clause, assign the
    /// negations of its literals one by one with propagation; a literal
    /// found true is implied by the ones before it (the clause shrinks to
    /// them plus it), one found false is dropped, a conflict ends the
    /// clause at the literals so far.  At most 2 M propagations a round;
    /// the saved phases are restored afterwards.
    fn vivify(&mut self) {
        let saved_phase = self.phase.clone();
        let budget_end = self.stats.propagations + 2_000_000;
        let mut cands: Vec<usize> = (self.first_learnt..self.clauses.len()).filter(|&ci| !self.deleted[ci] && self.learnt_lbd[ci - self.first_learnt] <= 6 && self.clauses[ci].len() > 2).collect();
        cands.sort_by_key(|&ci| (self.learnt_lbd[ci - self.first_learnt], self.clauses[ci].len()));
        for ci in cands {
            if self.stats.propagations > budget_end { break; }
            let lits = self.clauses[ci].clone();
            // under the level-0 assignment
            if lits.iter().any(|&l| self.lit_value(l) == Val::T) { self.deleted[ci] = true; self.clauses[ci] = Vec::new(); continue; }
            let lits: Vec<u32> = lits.into_iter().filter(|&l| self.lit_value(l) != Val::F).collect();
            self.deleted[ci] = true;   // out of the way of its own propagation
            let mut kept: Vec<u32> = Vec::new();
            let mut shortened = false;
            let mut conflict = false;
            for &l in &lits {
                match self.lit_value(l) {
                    Val::T => { kept.push(l); shortened = true; break; }   // implied by the negations so far
                    Val::F => { shortened = true; continue; }                 // dropped
                    Val::U => {
                        kept.push(l);
                        self.new_level();
                        self.assign(l >> 1, if l & 1 == 1 { Val::T } else { Val::F }, Reason::None);   // ¬l
                        if self.propagate().is_some() { conflict = true; break; }
                    }
                }
            }
            self.backjump(0);
            if conflict && kept.len() < lits.len() { shortened = true; }
            if !shortened || kept.len() == lits.len() { self.deleted[ci] = false; continue; }
            self.stats.vivified += 1;
            self.stats.vivified_lits += (lits.len() - kept.len()) as u64;
            self.clauses[ci] = Vec::new();
            let lbd = self.learnt_lbd[ci - self.first_learnt];
            let act = self.learnt_act[ci - self.first_learnt];
            self.add_learned(kept, lbd, act);
            if self.unsat_at_init { break; }
        }
        self.phase = saved_phase;
    }

    /// Add a learned clause at level 0 (an inprocessing result): a unit is
    /// assigned, the empty clause makes the engine unsatisfiable.
    fn add_learned(&mut self, mut c: Vec<u32>, lbd: u32, act: f64) {
        c.sort_unstable(); c.dedup();
        match c.len() {
            0 => self.unsat_at_init = true,
            1 => { let l = c[0]; if !self.assign(l >> 1, if l & 1 == 1 { Val::F } else { Val::T }, Reason::None) { self.unsat_at_init = true; } else if self.propagate().is_some() { self.unsat_at_init = true; } }
            _ => {
                let ci = self.clauses.len() as u32;
                self.watches[c[0] as usize].push((ci, c[1]));
                self.watches[c[1] as usize].push((ci, c[0]));
                self.clauses.push(c);
                self.deleted.push(false);
                self.learnt_lbd.push(lbd);
                self.learnt_act.push(act);
            }
        }
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
                let trail_len = self.trail.len() as u32;
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
                let mut lbd = 1;
                if learnt.len() == 1 {
                    self.assign(l0 >> 1, if l0 & 1 == 1 { Val::F } else { Val::T }, Reason::None);
                } else {
                    let ci = self.clauses.len() as u32;
                    self.watches[learnt[0] as usize].push((ci, learnt[1]));
                    self.watches[learnt[1] as usize].push((ci, learnt[0]));
                    lbd = self.lbd(&learnt);
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
                if self.restart_due(lbd, trail_len, conflicts_here, restarts) {
                    restarts += 1; conflicts_here = 0;
                    self.restart(base);
                    if self.inprocess && base == 0 && self.stats.conflicts >= self.inprocess_at {
                        self.inprocess_at = self.stats.conflicts + self.inprocess_interval;
                        self.inprocess_interval += 10_000;
                        self.backjump(0);
                        self.inprocess_round();
                        if self.unsat_at_init { return Verdict::Unsat; }
                    }
                }
                continue;
            }
            if let Some(max) = self.max_decisions && self.stats.decisions >= max { return Verdict::Unknown; }
            if self.stats.decisions & 255 == 0 && let Some(c) = &self.cancel && c.load(std::sync::atomic::Ordering::Relaxed) { return Verdict::Unknown; }
            if self.phases { self.update_phases(); }
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
            // VSIDS decision: the most active unassigned variable (assigned
            // ones still in the heap are dropped as they surface)
            let mut best: Option<u32> = None;
            while let Some(v) = self.heap_pop() {
                if self.vals[v as usize] == Val::U && !self.eliminated[v as usize] { best = Some(v); break; }
            }
            let Some(v) = best else { return Verdict::Sat(self.vals.iter().map(|&x| x == Val::T).collect()) };
            let v = v as usize;
            self.new_level();
            self.stats.decisions += 1;
            let ph = if self.phases && self.stable && self.target_size > 0 { self.target_phase[v] } else { self.phase[v] };
            self.assign(v as u32, if ph { Val::T } else { Val::F }, Reason::None);
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

    /// `simplify` (bounded variable elimination) on random 3-SAT near the
    /// threshold and on random tables with clauses, against brute force: the
    /// verdicts agree and the reconstructed models satisfy the *original*
    /// clauses, eliminated variables included.
    #[test]
    fn simplify_vs_bruteforce() {
        let mut seed: u64 = 0x5EED_0F_E11A_1234;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut eliminated_total = 0u64;
        for trial in 0..300 {
            let n = 4 + (rnd() % 9) as usize;
            let m = 2 + (rnd() % (5 * n as u64)) as usize;
            let mut cls: Vec<Vec<i32>> = Vec::new();
            for _ in 0..m {
                let len = 1 + (rnd() % 3) as usize;
                let mut c = Vec::new();
                for _ in 0..len { let v = (rnd() % n as u64) as i32 + 1; c.push(if rnd() % 2 == 0 { v } else { -v }); }
                cls.push(c);
            }
            // sometimes a table over a few variables too (its variables stay frozen)
            let boxes: Vec<Vec<Vec<Lit>>> = if rnd() % 2 == 0 {
                let k = 2 + (rnd() % 3) as usize;
                let mut cols: Vec<u32> = Vec::new();
                while cols.len() < k.min(n) { let v = (rnd() % n as u64) as u32; if !cols.contains(&v) { cols.push(v); } }
                let nrows = 1 + (rnd() % 5) as usize;
                let mut rows = Vec::new();
                for _ in 0..nrows {
                    let mut row = Vec::new();
                    for &v in &cols { if rnd() % 3 != 0 { let neg = rnd() % 2 == 0; row.push(Lit { var: v, neg }); } }
                    rows.push(row);
                }
                vec![rows]
            } else { Vec::new() };
            let row_holds = |row: &[Lit], m: &[bool]| row.iter().all(|l| m[l.var as usize] == !l.neg);
            let holds = |m: &[bool]| boxes.iter().all(|rows| rows.iter().any(|r| row_holds(r, m))) && check_model(&cls, m);
            let brute = (0..1u32 << n).any(|bits| holds(&(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let mut e = Engine::from_cnf(n, &cls);
            for rows in &boxes { e.add_box(TableBox::new(rows.clone())); }
            let ok = e.simplify();
            eliminated_total += e.stats.eliminated;
            let v = if ok { e.solve() } else { Verdict::Unsat };
            match v {
                Verdict::Sat(model) => { assert!(brute, "trial {trial}: engine SAT, brute UNSAT"); assert!(holds(&model), "trial {trial}: reconstructed model violates the original {cls:?} {boxes:?}"); }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT: {cls:?} {boxes:?}"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
        assert!(eliminated_total > 0, "simplify never eliminated a variable");
        // pigeonhole survives elimination
        let (n, c) = php(4, 3);
        let mut e = Engine::from_cnf(n, &c);
        assert!(e.simplify());
        assert_eq!(e.solve(), Verdict::Unsat);
    }

    /// Inprocessing (re-elimination, vivification) and rephasing forced to
    /// run every few conflicts on random 3-SAT of 70 variables near the
    /// threshold, under both restart policies, against CaDiCaL; models are
    /// checked against the clauses.
    #[test]
    fn inprocessing_vs_cadical() {
        let mut seed: u64 = 0x1F1F_2E2E_3D3D_4C4C;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let (n, m) = (70usize, 298usize);
        let mut rounds = 0u64; let mut vivified = 0u64;
        for trial in 0..20 {
            let mut cls: Vec<Vec<i32>> = Vec::new();
            for _ in 0..m {
                let mut c = Vec::new();
                while c.len() < 3 { let v = (rnd() % n as u64) as i32 + 1; if !c.iter().any(|&x: &i32| x.abs() == v) { c.push(if rnd() % 2 == 0 { v } else { -v }); } }
                cls.push(c);
            }
            let mut cad: cadical::Solver<cadical::Timeout> = cadical::Solver::new();
            for c in &cls { cad.add_clause(c.iter().copied()); }
            let expect = cad.solve().expect("cadical");
            let mut e = Engine::from_cnf(n, &cls);
            e.inprocess_at = 30; e.inprocess_interval = 30; e.rephase_at = 20; e.reduce_start = 50;
            e.inprocess = true; e.phases = true;
            e.restart = if trial % 2 == 0 { RestartMode::Luby } else { RestartMode::Glucose };
            let ok = e.simplify();
            let v = if ok { e.solve() } else { Verdict::Unsat };
            rounds += e.stats.inprocess_rounds; vivified += e.stats.vivified;
            match v {
                Verdict::Sat(model) => { assert!(expect, "trial {trial}: engine SAT, CaDiCaL UNSAT"); assert!(check_model(&cls, &model), "trial {trial}: bad model"); }
                Verdict::Unsat => assert!(!expect, "trial {trial}: engine UNSAT, CaDiCaL SAT"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
        eprintln!("inprocessing rounds {rounds}, clauses vivified {vivified}");
        assert!(rounds > 0, "no inprocessing round ran — lower the interval or raise m");
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
        // php(7,6) needs thousands of conflicts whatever the minimisation: deletions for sure
        let (n, c) = php(7, 6);
        let mut e = Engine::from_cnf(n, &c);
        e.reduce_start = 8;
        assert_eq!(e.solve(), Verdict::Unsat);
        let ndel = e.deleted.iter().filter(|&&d| d).count();
        eprintln!("php(7,6): {} conflicts, {} learned, {ndel} deleted", e.stats.conflicts, e.clauses.len() - e.first_learnt);
        deletions_seen |= ndel > 0;
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
