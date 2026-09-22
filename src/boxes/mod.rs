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

/// Does box constrainedness say anything about where the search fails?
///
/// §3.4 of the design doc specifies branching on the box with the fewest
/// live rows — the fail-first / MRV argument that a box near failing is the
/// cheapest place to discover the failure.  The premise is testable without
/// building the heuristic: at every conflict, ask where the conflicting
/// box's live count ranked among all boxes *at the moment of the preceding
/// decision*, which the per-level snapshots already hold.
///
/// Uniform deciles mean constrainedness says nothing about which box fails
/// next, and every heuristic built on it is dead on arrival.  Concentration
/// in the lowest decile is necessary evidence and not sufficient: this
/// samples the trajectory VSIDS takes, and an MRV-driven search would take
/// a different one.
///
/// `BOXES_EFF_STUDY=1`; off by default because ranking costs O(boxes) per
/// conflict.
#[derive(Default, Debug, Clone)]
pub struct EffStudy {
    /// Conflicts by where they came from.  A box-guided decision heuristic
    /// can only steer the box ones, so this ratio bounds what it could buy
    /// — and on a plain CNF, where every constraint is a watched clause and
    /// `hdr` is empty, it bounds it at nothing.
    pub box_conflicts: u64,
    pub clause_conflicts: u64,
    /// Of the clause conflicts, those in a *learned* clause.  The
    /// distinction bounds the translator: an original clause that keeps
    /// producing conflicts is one a bigger or better-shaped box could have
    /// absorbed, and a learned clause is one no translator can ever reach,
    /// because it did not exist when the instance was compiled.
    pub clause_conflicts_learned: u64,
    /// Box conflicts with a preceding decision to rank against, and those
    /// at level 0 with none.
    pub sampled: u64,
    pub unsampled: u64,
    /// Where the conflicting box ranked; `deciles[0]` is the most
    /// constrained tenth.
    pub deciles: [u64; 10],
    /// It was among the most constrained boxes, and among the ten most
    /// constrained.  Ties count in the box's favour, so both are upper
    /// bounds on what a heuristic could actually hit.
    pub top1: u64,
    pub top10: u64,
    /// Live rows of the conflicting box, summed over samples, against the
    /// all-box mean summed once per sample — both as of that decision.
    pub conflict_rows: u64,
    pub population_rows: f64,
    /// The same ranking by *fraction* of rows still live rather than by
    /// count.  §3.4 says "fewest live rows" literally, but a raw count
    /// conflates being tightly constrained now with having been a big table
    /// to begin with — a K = 8 cone can start with 256 rows and a small one
    /// with 4 — and the CSP heuristic this lifts compares domains against
    /// their own size.  Both readings get measured.
    pub deciles_frac: [u64; 10],
    pub top1_frac: u64,
    pub conflict_frac: f64,
    pub population_frac: f64,
    /// Initial table size of the conflicting box against the mean, which
    /// exposes that confound directly.
    pub conflict_nrows: u64,
    pub population_nrows: f64,
}

/// One clause the search kept failing on: the seed for mining a box out of
/// the region it belongs to.
///
/// A box's power over a group of clauses is GAC on their *conjunction*,
/// which unit propagation does not give — UP achieves arc consistency on
/// each clause separately.  So any group of clauses sharing variables is a
/// box candidate, and the ones worth trying first are the ones the search
/// demonstrably keeps failing on.
#[derive(Clone, Debug)]
pub struct EffClause {
    pub lits: Vec<i32>,
    pub conflicts: u32,
    pub learned: bool,
    /// Literal block distance (learned clauses only): how many decision
    /// levels the clause spans, i.e. how *local* it is.  A box wants local
    /// clauses — their variables cluster, so the table stays small — and a
    /// low LBD also means the clause is one `reduce_db` keeps.
    pub lbd: u32,
    pub activity: f64,
    pub deleted: bool,
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub decisions: u64,
    pub propagations: u64,
    pub conflicts: u64,
    /// Propagation's work, counted under `BOXES_COUNT_VISITS`: entries of
    /// binary lists visited; entries of long-clause watch lists visited,
    /// of which skipped by a true blocker; clauses whose literals were
    /// read; literal steps taken looking for a replacement watch.
    pub bin_visits: u64,
    pub watch_visits: u64,
    pub blocker_hits: u64,
    pub clause_visits: u64,
    pub lit_steps: u64,
    /// Table explanations computed (conflicts and reasons), the literals
    /// they contained, and the literals minimisation dropped.
    pub explanations: u64,
    pub explanation_lits: u64,
    pub explanation_dropped: u64,
    /// Reason explanations served from the per-assignment cache.
    pub explanation_hits: u64,
    /// Table reasons taken from an explanation-only gate clause instead.
    pub explanation_gate: u64,
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
    /// Subsumption rounds, clauses subsumed away, and clauses strengthened
    /// by self-subsuming resolution (with the literals they lost).
    /// Branching-heuristic study (`BOXES_EFF_STUDY=1`), all zero otherwise.
    pub eff: EffStudy,
    /// Learned-clause shrinking: level blocks replaced by their block UIP,
    /// blocks tried, and the literals removed.
    /// Conflicts resolved by backtracking one level instead of to the
    /// asserting level, and literals kept by backtracking out of order.
    pub chrono_backtracks: u64,
    pub chrono_kept: u64,
    pub shrink_blocks: u64,
    pub shrink_tried: u64,
    pub shrunk_lits: u64,
    pub subsume_rounds: u64,
    pub subsumed: u64,
    pub strengthened: u64,
    pub strengthened_lits: u64,
    pub rephases: u64,
    /// Learned clauses whose recomputed LBD beat the one they were born
    /// with, and clauses a reduction spared because analysis had used them.
    pub promoted: u64,
    pub spared: u64,
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
    Glucose,
    /// CaDiCaL's focused-mode restarts: a fast (1/33) and a slow (1/10⁵)
    /// bias-corrected exponential moving average of learned-clause LBD, and a
    /// restart whenever fast exceeds slow by `restart_margin` (1.10) after
    /// at least two conflicts — no queue to refill, no blocking.  Stable
    /// phases alternate as for `Glucose` unless `BOXES_STABLE=0`.
    ///
    /// Why it exists (2026-09-17): the engine restarted once per ~700
    /// conflicts on c3540 where CaDiCaL restarts once per 20, and CaDiCaL's
    /// own ablation there puts restarts at 2.7-4.3x its conflict count.
    ///
    /// The default since 2026-09-17: over 17 verdict-checked refutations it
    /// needs 1.11x fewer conflicts than `Glucose` (1.52x CaDiCaL's count
    /// instead of 1.69x), consistently on the c3540/c5315 shuffles and worse
    /// on four single combinatorial instances (RoundRobin 10/8, w(5;5;178),
    /// pyhala-braun-unsat-40, Steiner-45).
    #[default]
    Ema,
}

/// An exponential moving average with Biere and Fröhlich's bias correction
/// ("Evaluating CDCL restart schemes", 2015): early values are not dragged
/// towards the zero it starts from.
#[derive(Clone, Copy, Debug)]
pub struct Ema { alpha: f64, biased: f64, exp: f64, pub value: f64 }

impl Ema {
    pub fn new(alpha: f64) -> Ema { Ema { alpha, biased: 0.0, exp: 1.0, value: 0.0 } }
    pub fn update(&mut self, y: f64) {
        self.biased += self.alpha * (y - self.biased);
        if self.exp > 0.0 {
            self.exp *= 1.0 - self.alpha;
            self.value = self.biased / (1.0 - self.exp);
            if self.exp < 1e-12 { self.exp = 0.0; }
        } else {
            self.value = self.biased;
        }
    }
}

impl RestartMode {
    /// `BOXES_RESTART=luby|glucose`, default `glucose`.
    pub fn from_env() -> RestartMode {
        match std::env::var("BOXES_RESTART").as_deref() { Ok("luby") => RestartMode::Luby, Ok("glucose") => RestartMode::Glucose, _ => RestartMode::Ema }
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

/// What a clause's `used` counter is set to when conflict analysis
/// resolves it, and therefore how many reductions it can survive unused.
/// CaDiCaL's value; it has to fit in a clause header there, and matches
/// the two sparing rules in [`Engine::reduce_db`]: `used > 0` means "used
/// within the last 31 reductions" (a long tier-1 lifespan) and
/// `used >= MAX_USED - 1` means "used since the last one" (a short tier-2
/// grace).
const MAX_USED: u8 = 31;

/// This process's peak resident size in bytes (macOS reports bytes, Linux
/// kilobytes).  Resident undercounts a footprint the kernel has compressed,
/// but at the points this is read nothing has gone cold yet.
fn peak_rss_bytes() -> usize {
    let mut ru: libc::rusage = unsafe { std::mem::zeroed() };
    if unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut ru) } != 0 { return 0; }
    if cfg!(target_os = "macos") { ru.ru_maxrss as usize } else { ru.ru_maxrss as usize * 1024 }
}

/// The process's physical footprint right now: what Activity Monitor
/// charges it, compressed and swapped pages included, which RSS drops.
/// The peak says how high the water got; this says what is live at a
/// checkpoint, so the two together locate a transient.
/// What the allocator holds: (bytes handed out and live, bytes freed but
/// kept for reuse).  Footprint minus the sum is what the process maps
/// outside malloc; the second number is fragmentation.  macOS only.
fn malloc_stats() -> (usize, usize) {
    #[cfg(target_os = "macos")]
    { let m = unsafe { libc::mstats() }; return (m.bytes_used, m.bytes_free); }
    #[allow(unreachable_code)] (0, 0)
}

fn cur_footprint_bytes() -> usize {
    #[cfg(target_os = "macos")]
    {
        // libmalloc keeps freed large blocks until reuse or memory
        // pressure, and the process is charged for them meanwhile: a
        // 1.2 GB pool dropped in the elimination round did not move the
        // footprint at all.  Asking for the release first makes the
        // reading the live memory, which is what a checkpoint is for.
        unsafe extern "C" { fn malloc_zone_pressure_relief(zone: *mut libc::c_void, goal: usize) -> usize; }
        unsafe { malloc_zone_pressure_relief(std::ptr::null_mut(), 0); }
        let mut ri: libc::rusage_info_v2 = unsafe { std::mem::zeroed() };
        let rc = unsafe { libc::proc_pid_rusage(std::process::id() as libc::c_int, libc::RUSAGE_INFO_V2,
                                                 &mut ri as *mut libc::rusage_info_v2 as *mut libc::rusage_info_t) };
        if rc == 0 { return ri.ri_phys_footprint as usize; }
    }
    #[cfg(target_os = "linux")]
    {
        if let Ok(t) = std::fs::read_to_string("/proc/self/statm") {
            if let Some(r) = t.split_whitespace().nth(1).and_then(|x| x.parse::<usize>().ok()) { return r * 4096; }
        }
    }
    0
}

/// Bytes a `Vec` holds, counting capacity: slack is resident once it has
/// been written through, and a doubled buffer's slack is the cost.
fn vec_bytes<T>(v: &[T]) -> usize { v.len() * std::mem::size_of::<T>() }
fn vec_cap_bytes<T>(v: &Vec<T>) -> usize { v.capacity() * std::mem::size_of::<T>() }
/// A `Vec<Vec<T>>`: the outer buffer of 24-byte headers plus every inner
/// buffer's capacity.  Returns (bytes, inner vecs).
fn vecvec_bytes<T>(v: &Vec<Vec<T>>) -> (usize, usize) {
    (v.capacity() * std::mem::size_of::<Vec<T>>() + v.iter().map(vec_cap_bytes).sum::<usize>(), v.len())
}

/// Read a `usize` knob from the environment (experiment support: the
/// clause-database policy is the one CDCL lever with no A/B behind it).
fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

/// The clauses removed by variable elimination, kept for `reconstruct`:
/// per eliminated variable, in elimination order, the clauses that went
/// with it.  Two levels of end offsets over one literal array -- a Vec per
/// clause was 507 MB for 9 M small clauses on the 40 M-clause instance
/// (2026-09-21), most of it headers and allocator rounding, and 9 M small
/// allocations interleaved with the occurrence lists' growth.
#[derive(Default)]
struct ElimStore {
    var: Vec<u32>,     // the eliminated variable
    cend: Vec<u32>,    // per variable: end of its clauses in the clause table
    lend: Vec<u32>,    // per clause: end of its literals in `lits`
    lits: Vec<u32>,
}
impl ElimStore {
    fn push_clause(&mut self, c: &[u32]) { self.lits.extend_from_slice(c); self.lend.push(self.lits.len() as u32); }
    /// Close the variable whose clauses were just pushed.
    fn push_var(&mut self, v: u32) { self.var.push(v); self.cend.push(self.lend.len() as u32); }
    fn len(&self) -> usize { self.var.len() }
    fn clause(&self, j: usize) -> &[u32] {
        let l0 = if j == 0 { 0 } else { self.lend[j - 1] as usize };
        &self.lits[l0..self.lend[j] as usize]
    }
    /// The clause-table range of variable `i`.
    fn clauses(&self, i: usize) -> std::ops::Range<usize> {
        (if i == 0 { 0 } else { self.cend[i - 1] as usize })..self.cend[i] as usize
    }
    fn cap_bytes(&self) -> usize { vec_cap_bytes(&self.var) + vec_cap_bytes(&self.cend) + vec_cap_bytes(&self.lend) + vec_cap_bytes(&self.lits) }
    fn used_bytes(&self) -> usize { vec_bytes(&self.var) + vec_bytes(&self.cend) + vec_bytes(&self.lend) + vec_bytes(&self.lits) }
}

/// Per-literal lists in one arena: list `l` is
/// `data[start[l] .. start[l] + len[l]]` with `cap[l]` slots reserved.  A
/// list that outgrows its slot moves to the end of the arena with twice
/// the room, and the hole it leaves is reclaimed by `defrag` at a safe
/// point (nothing holds an index across it).  Twelve bytes per literal
/// instead of a 24-byte `Vec` header and a malloc block each: the watch
/// and binary lists of 14.6 M literals were 700 MB of headers on the
/// 40 M-clause instance (2026-09-21).  Order within a list is exactly a
/// `Vec`'s, so propagation visits the same clauses in the same order.
#[derive(Default)]
struct Lists {
    data: Vec<(u32, u32)>,
    start: Vec<u32>,
    len: Vec<u32>,
    cap: Vec<u32>,
    /// slots of `data` no list owns
    holes: usize,
}
impl Lists {
    fn n(&self) -> usize { self.start.len() }
    fn resize(&mut self, n: usize) { self.start.resize(n, 0); self.len.resize(n, 0); self.cap.resize(n, 0); }
    #[inline] fn range(&self, l: usize) -> std::ops::Range<usize> {
        let s = self.start[l] as usize;
        s..s + self.len[l] as usize
    }
    #[inline] fn push(&mut self, l: usize, w: (u32, u32)) {
        let n = self.len[l];
        if n >= self.cap[l] { self.relocate(l, (2 * self.cap[l]).max(4)); }
        self.data[self.start[l] as usize + n as usize] = w;
        self.len[l] = n + 1;
    }
    /// Move list `l` to the end of the arena with `newcap` slots.
    fn relocate(&mut self, l: usize, newcap: u32) {
        let (s, n) = (self.start[l] as usize, self.len[l] as usize);
        let ns = self.data.len();
        self.data.reserve(newcap as usize);
        self.data.extend_from_within(s..s + n);
        self.data.resize(ns + newcap as usize, (0, 0));
        self.holes += self.cap[l] as usize;
        self.start[l] = ns as u32;
        self.cap[l] = newcap;
    }
    /// Every list empty, the arena gone.
    fn clear(&mut self) {
        self.data = Vec::new();
        self.start.iter_mut().for_each(|x| *x = 0);
        self.len.iter_mut().for_each(|x| *x = 0);
        self.cap.iter_mut().for_each(|x| *x = 0);
        self.holes = 0;
    }
    /// Lay the (empty) lists out with exactly `counts[l]` slots each.
    fn layout_exact(&mut self, counts: &[u32]) {
        debug_assert!(self.len.iter().all(|&n| n == 0), "layout_exact over non-empty lists");
        debug_assert_eq!(counts.len(), self.n());
        let mut total = 0u64;
        for l in 0..self.n() { self.start[l] = total as u32; self.cap[l] = counts[l]; total += counts[l] as u64; }
        assert!(total <= u32::MAX as u64, "watch arena exceeds u32 indexing");
        self.data = vec![(0, 0); total as usize];
        self.holes = 0;
    }
    /// Reclaim the holes: every list contiguous in literal order, room
    /// exactly for its entries.  Only where nothing holds an index.
    fn defrag(&mut self) {
        if self.holes < self.data.len() / 3 { return; }
        let live = self.data.len() - self.holes;
        let mut data: Vec<(u32, u32)> = Vec::with_capacity(live);
        for l in 0..self.n() {
            let r = self.range(l);
            self.start[l] = data.len() as u32;
            self.cap[l] = self.len[l];
            data.extend_from_slice(&self.data[r]);
        }
        self.data = data;
        self.holes = 0;
    }
    fn cap_bytes(&self) -> usize { vec_cap_bytes(&self.data) + vec_cap_bytes(&self.start) + vec_cap_bytes(&self.len) + vec_cap_bytes(&self.cap) }
    fn used_bytes(&self) -> usize { self.len.iter().map(|&n| n as usize * 8).sum::<usize>() + 12 * self.n() }
}

#[inline] fn code(var: u32, neg: bool) -> u32 { var << 1 | neg as u32 }

/// Capacity to reserve for a clause store holding `n` of something
/// (literals, clauses) with the learned clauses still to come: a quarter
/// more, at least `min_extra`.  Capacity nobody writes is free, while the
/// first learned clause pushing past an exact reservation doubles the
/// store -- a copy of the whole arena, and twice its capacity (568 MB on
/// the 40 M-clause instance, 2026-09-21).
#[inline] fn with_headroom(n: usize, min_extra: usize) -> usize { n + n / 4 + min_extra }

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
    /// Live rows per box — the popcount of its words in `live`, i.e. §3.4's
    /// "effective path count": the exact number of paths the box still
    /// admits under the trail, not an estimate of it.
    ///
    /// Maintained **only under `eff_study`**.  It is cheap (every writer of
    /// `live` already touches each word, and it made the dead-box test a
    /// counter read instead of a scan) but it still measured 1.019× on the
    /// cone corpus, and after the 2026-09-18 study nothing reads it in a
    /// normal run — see [`EffStudy`] for why no heuristic was built on it.
    live_count: Vec<u32>,
    /// Snapshots of `live_count`, in step with `snap`.
    snap_count: Vec<u32>,
    /// Sample the branching-heuristic premise (`BOXES_EFF_STUDY=1`).
    eff_study: bool,
    /// Conflicts per box, under `eff_study` — see [`Engine::eff_concentration`].
    eff_box_hits: Vec<u32>,
    /// Conflicts per clause, under `eff_study` — see
    /// [`Engine::eff_clause_dump`].  Indexed by clause index, so it is
    /// cleared wherever `simplify` rebuilds the clause store.
    eff_clause_hits: Vec<u32>,
    /// Snapshots of `live` at the start of each open decision level.
    snap: Vec<u64>,
    in_queue: Vec<bool>,
    queue: Vec<u32>,
    // clauses
    /// The clause store: clause `ci` is `arena[cstart[ci] .. + clen[ci]]`,
    /// contiguous so a watch visit touches one cache line; a deleted clause
    /// keeps its index with `clen` 0 and `reduce_db` compacts the arena.
    arena: Vec<u32>,
    cstart: Vec<u32>,
    clen: Vec<u32>,
    /// Per literal code: the clauses watching it (visited when it becomes
    /// FALSE), each with a blocker literal, as `(clause, blocker)`.  Binary
    /// clauses are not here:
    watches: Lists,
    /// per literal code, the literals a binary clause implies when it
    /// becomes FALSE, with the clause, as `(literal, clause)` (never deleted).
    bins: Lists,
    /// Explanation-only clauses (`add_explain_clause`): a cone's gate
    /// clauses kept beside its table, never propagated; when the table
    /// forces a literal and one of them is unit for it under the earlier
    /// assignment, that clause is the reason instead of the table's cover.
    xarena: Vec<u32>,
    xstart: Vec<u32>,
    xlen: Vec<u32>,
    /// per literal code: the explanation-only clauses containing it
    xidx: Vec<Vec<u32>>,
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
    /// How much the interval grows per reduction (`BOXES_REDUCE_STEP`).
    reduce_step: usize,
    /// Fraction of the learned database a reduction drops: `1/reduce_frac`
    /// of the surviving clauses, worst first (`BOXES_REDUCE_FRAC`).
    reduce_frac: usize,
    /// Learned clauses of at most this LBD are never deleted
    /// (`BOXES_KEEP_LBD`; CaDiCaL's "core" tier).
    keep_lbd: u32,
    /// Tier-2 bound: a clause at or below this LBD is spared a reduction
    /// if conflict analysis resolved it since the previous one.  This is
    /// the grace period CaDiCaL's `used` counter buys, and the one part of
    /// its reduce policy that measured worth having — collapsing tier 2
    /// into tier 1 cost CaDiCaL 1.30×
    /// (`doc/data/boxes_reduce_policy_2026-09-18.txt`).
    tier2_lbd: u32,
    /// Percent of the *candidate* set a reduction drops once the grace
    /// period is on.  CaDiCaL's 75, against our `reduce_frac`'s fraction of
    /// the whole database — the pools are not the same thing.
    reduce_target: usize,
    /// Reductions a learned clause may still survive unused; `MAX_USED`
    /// when analysis last resolved it, decremented once per reduction.
    learnt_used: Vec<u8>,
    /// `BOXES_USED=1`: spare recently-used clauses and target the
    /// candidate set.  `BOXES_PROMOTE=1`: also recompute a resolved
    /// clause's LBD and promote it when the glue shrinks.
    used_grace: bool,
    promote: bool,
    /// Level stamps for recomputing LBD without allocating, and the
    /// generation that makes clearing them unnecessary.
    lbd_stamp: Vec<u64>,
    lbd_gen: u64,
    unsat_at_init: bool,
    // assignment
    vals: Vec<Val>,
    /// Per literal code: its value (`lit_value` is one load).
    lvals: Vec<Val>,
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
    /// Learned-clause shrinking (`BOXES_SHRINK=1` turns it on; off until its
    /// A/B says otherwise): per variable, marked while its block is shrunk.
    pub shrink: bool,
    shrink_mark: Vec<bool>,
    /// Chronological backtracking (Nadel and Ryvchin, SAT 2018; Möhle and
    /// Biere, "Backing Backtracking", SAT 2019), `BOXES_CHRONO=1`.  A literal
    /// implied by a clause takes the highest level among the clause's other
    /// literals, which may be below the current decision level; a backjump
    /// keeps every literal whose level survives it, wherever it sits on the
    /// trail; and a conflict whose asserting level is more than
    /// `chrono_levels` below it backtracks one level instead of all the way.
    pub chrono: bool,
    pub chrono_levels: usize,
    /// Trail reuse on backjumps (`BOXES_CHRONO_REUSE=0` turns it off; only
    /// with `chrono`): CaDiCaL's `chronoreusetrail`, read from its source.
    /// Among the literals assigned above the asserting level, take the most
    /// active variable and backtrack only to the level that keeps it.
    /// CaDiCaL's own ablation on c3540 puts this at 2.03x its conflict count
    /// — the whole of its chronological-backtracking benefit there.
    pub chrono_reuse: bool,
    /// `BOXES_DEBUG_WATCHES=1`: check the watch invariant during search.
    debug_watches: bool,
    chrono_kept_scratch: Vec<u32>,
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
    /// `BOXES_STABLE=1`: alternate focused and stable phases.  Off by default:
    /// the engine's stable phase is Luby restarts with the same decision
    /// heuristic and phases, and on the verdict-checked set it costs
    /// conflicts with either restart mode (CaDiCaL's own ablation finds its
    /// far stronger stable mode a loss on the circuits too, 0.57-0.72x).
    pub stabilize: bool,
    /// Fast and slow LBD averages for `RestartMode::Ema`, and its margin
    /// (`BOXES_RESTART_MARGIN`, default 1.10).
    glue_fast: Ema,
    glue_slow: Ema,
    pub restart_margin: f64,
    stable_len: u64,
    stable_toggle_at: u64,
    /// Variables `simplify` resolved away (never decided) and, per
    /// elimination in order, the clauses removed with it — replayed
    /// backwards to extend a model.
    eliminated: Vec<bool>,
    elim: ElimStore,
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
    /// Subsumption and self-subsuming resolution at level 0
    /// (`BOXES_SUBSUME=0` turns it off).  CaDiCaL subsumes a fifth to two
    /// fifths of the clauses on the instances this engine is behind on and
    /// the engine had none of it (§10.1, 2026-09-16).
    pub subsume: bool,
    subsume_at: u64,
    subsume_interval: u64,
    pub stats: Stats,
    /// Optional decision budget; `solve` returns `Unknown` when exceeded.
    pub max_decisions: Option<u64>,
    /// Cooperative cancellation: checked every 256 conflicts or decisions
    /// and every 4096 propagated literals; `solve` returns `Unknown`.
    pub cancel: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    /// `cancel` seen set inside `propagate`, which then returns early with
    /// the trail not fully propagated; the search returns `Unknown` next.
    /// On a 7 M-variable instance 256 decisions took longer than the
    /// watchdog's grace and the timeout lost the statistics (2026-09-21).
    cancelled: bool,
    /// `BOXES_COUNT_VISITS`: count propagation's work (see `Stats`).
    count_visits: bool,
    /// How table explanations are chosen.
    pub explain: ExplainMode,
    // scratch for `explain_box`: (class, level, trail position, local index, kill-mask base)
    expl_cands: Vec<(u8, u32, u32, u32, u32)>,
    expl_orig: Vec<u64>,
    expl_picked: Vec<(u32, u32, u8)>,
    expl_keep: Vec<bool>,
    expl_used: Vec<bool>,
    // ── proof logging (§4 of the design doc; `proof.rs`) ──────────────
    /// DRAT sink for the refutation; `None` (the default) logs nothing.
    pub proof: Option<proof::Proof>,
    /// The clauses the plugged-in boxes stand for in the original formula.
    /// A box propagation is justified against these; without them the proof
    /// of a boxed run is incomplete.
    box_src: Vec<Vec<i32>>,
    /// The sub-engine that derives box lemmas from `box_src` (built on
    /// first use, holds no boxes, so its own learned clauses are ordinary
    /// RUP additions).
    justifier: Option<Box<Engine>>,
    /// Box lemmas already emitted, as sorted literal codes.
    lemma_seen: std::collections::HashSet<Vec<u32>>,
    /// Level-0 trail entries whose box reasons have been justified.
    proof_l0: usize,
}

impl Engine {
    pub fn new(nvars: usize, boxes: Vec<TableBox>) -> Engine {
        let mut e = Engine {
            nvars: 0, hdr: Vec::new(), vars_all: Vec::new(), kill_all: Vec::new(), occ: Vec::new(), live: Vec::new(), live_count: Vec::new(), snap_count: Vec::new(),
            eff_study: matches!(std::env::var("BOXES_EFF_STUDY").as_deref(), Ok("1") | Ok("on")),
            eff_box_hits: Vec::new(),
            eff_clause_hits: Vec::new(),
            snap: Vec::new(), in_queue: Vec::new(), queue: Vec::new(),
            arena: Vec::new(), cstart: Vec::new(), clen: Vec::new(), watches: Lists::default(), bins: Lists::default(), first_learnt: 0,
            xarena: Vec::new(), xstart: Vec::new(), xlen: Vec::new(), xidx: Vec::new(),
            learnt_lbd: Vec::new(), learnt_act: Vec::new(), deleted: Vec::new(), cla_inc: 1.0, reduce_at: 0,
            reduce_start: env_usize("BOXES_REDUCE_START", 4000),
            reduce_step: env_usize("BOXES_REDUCE_STEP", REDUCE_STEP),
            reduce_frac: env_usize("BOXES_REDUCE_FRAC", 2),
            keep_lbd: env_usize("BOXES_KEEP_LBD", 2) as u32,
            tier2_lbd: env_usize("BOXES_TIER2_LBD", 6) as u32,
            reduce_target: env_usize("BOXES_REDUCE_TARGET", 75),
            learnt_used: Vec::new(),
            used_grace: matches!(std::env::var("BOXES_USED").as_deref(), Ok("1") | Ok("on")),
            promote: matches!(std::env::var("BOXES_PROMOTE").as_deref(), Ok("1") | Ok("on")),
            lbd_stamp: Vec::new(), lbd_gen: 0,
            unsat_at_init: false,
            vals: Vec::new(), lvals: Vec::new(), level: Vec::new(), reason: Vec::new(), trail_pos: Vec::new(),
            trail: Vec::new(), trail_lim: Vec::new(), qhead: 0,
            activity: Vec::new(), var_inc: 1.0, phase: Vec::new(), seen: Vec::new(),
            heap: Vec::new(), heap_pos: Vec::new(),
            minimize: !matches!(std::env::var("BOXES_MINIMIZE").as_deref(), Ok("0") | Ok("none") | Ok("off")),
            min_stack: Vec::new(), min_clear: Vec::new(), min_lits: Vec::new(),
            shrink: matches!(std::env::var("BOXES_SHRINK").as_deref(), Ok("1") | Ok("on")),
            shrink_mark: Vec::new(),
            chrono: matches!(std::env::var("BOXES_CHRONO").as_deref(), Ok("1") | Ok("on")),
            chrono_levels: env_usize("BOXES_CHRONO_LEVELS", 100),
            chrono_reuse: !matches!(std::env::var("BOXES_CHRONO_REUSE").as_deref(), Ok("0") | Ok("off")),
            debug_watches: std::env::var("BOXES_DEBUG_WATCHES").is_ok(),
            chrono_kept_scratch: Vec::new(),
            expl_cache: Vec::new(), expl_ok: Vec::new(),
            restart: RestartMode::from_env(),
            lbd_q: std::collections::VecDeque::new(), lbd_q_sum: 0, lbd_sum: 0,
            trail_q: std::collections::VecDeque::new(), trail_q_sum: 0,
            stable: false, stable_len: 1000, stable_toggle_at: 1000,
            stabilize: matches!(std::env::var("BOXES_STABLE").as_deref(), Ok("1") | Ok("on")),
            glue_fast: Ema::new(1.0 / 33.0), glue_slow: Ema::new(1.0 / 1e5),
            restart_margin: std::env::var("BOXES_RESTART_MARGIN").ok().and_then(|v| v.parse().ok()).unwrap_or(1.10),
            eliminated: Vec::new(), elim: ElimStore::default(), elim_enabled: false,
            phases: matches!(std::env::var("BOXES_PHASES").as_deref(), Ok("1") | Ok("on")),
            target_phase: Vec::new(), target_size: 0, best_phase: Vec::new(), best_size: 0,
            rephase_at: 1000, rephase_count: 0, rng: 0x9E37_79B9_7F4A_7C15,
            inprocess: matches!(std::env::var("BOXES_INPROCESS").as_deref(), Ok("1") | Ok("on")),
            inprocess_at: 10_000, inprocess_interval: 10_000,
            subsume: !matches!(std::env::var("BOXES_SUBSUME").as_deref(), Ok("0") | Ok("off") | Ok("none")),
            subsume_at: env_usize("BOXES_SUBSUME_START", 2000) as u64,
            subsume_interval: env_usize("BOXES_SUBSUME_START", 2000) as u64,
            stats: Stats::default(), max_decisions: None, cancel: None, cancelled: false,
            count_visits: matches!(std::env::var("BOXES_COUNT_VISITS").as_deref(), Ok("1") | Ok("on")),
            explain: ExplainMode::from_env(),
            expl_cands: Vec::new(), expl_orig: Vec::new(), expl_picked: Vec::new(), expl_keep: Vec::new(), expl_used: Vec::new(),
            proof: None, box_src: Vec::new(), justifier: None, lemma_seen: Default::default(), proof_l0: 0,
        };
        e.grow(nvars);
        for b in boxes { e.add_box(b) }
        e
    }

    /// Every clause becomes a watched clause.
    /// Anything that yields clauses of DIMACS literals: a `&[Vec<i32>]`,
    /// or a `Cnf::iter()` on the flat form the parser now builds — the
    /// large-instance path must never have to materialise a `Vec` per
    /// clause just to get here.
    pub fn from_cnf<C: AsRef<[i32]>>(nvars: usize, clauses: impl IntoIterator<Item = C>) -> Engine {
        Self::from_cnf_sized(nvars, 0, 0, clauses)
    }

    /// `from_cnf` with the clause and literal counts known up front, so the
    /// clause store is reserved once instead of doubling its way up.  A
    /// doubling large buffer costs its own size again while it is copied,
    /// and on macOS the copy is charged to the process only as the pages
    /// are next touched, which hid ~0.8 GB of the 40 M-clause instance's
    /// build from every checkpoint (2026-09-21).
    pub fn from_cnf_sized<C: AsRef<[i32]>>(nvars: usize, nclauses: usize, nlits: usize,
                                          clauses: impl IntoIterator<Item = C>) -> Engine {
        let mut e = Engine::new(nvars, Vec::new());
        let (lit_cap, cl_cap) = (with_headroom(nlits, 1 << 20), with_headroom(nclauses, 1 << 17));
        e.arena.reserve_exact(lit_cap); e.cstart.reserve_exact(cl_cap); e.clen.reserve_exact(cl_cap);
        e.deleted.reserve_exact(cl_cap);
        let mut buf: Vec<Lit> = Vec::new();
        for c in clauses {
            buf.clear();
            buf.extend(c.as_ref().iter().map(|&l| lit_of_dimacs(l)));
            e.add_clause_impl(&buf, false);
        }
        e.attach_watches(0, e.cstart.len());
        e
    }

    /// Log the refutation to `p` as DRAT, checked against the formula this
    /// engine was built from plus [`set_box_source`](Self::set_box_source).
    ///
    /// Variable elimination and subsumption are logged: a resolvent is RUP
    /// against the clauses already in the proof, and a deletion never has to
    /// be emitted at all (dropping one only makes later checks harder).
    /// Inprocessing's vivification is left off, the trade hydra's certified
    /// mode makes for the GE-simplified residual (§4 of the design doc).
    pub fn set_proof(&mut self, p: proof::Proof) {
        self.proof = Some(p);
        self.inprocess = false;
    }

    /// The clauses the plugged-in boxes stand for.  Every box propagation is
    /// derived from these before the clause that used it is logged.
    pub fn set_box_source(&mut self, clauses: &[Vec<i32>]) {
        self.box_src = clauses.to_vec();
        self.justifier = None;
    }

    /// Log a derived clause.  Level-0 box reasons are justified first: the
    /// analysis drops level-0 literals from a learned clause, so the checker
    /// must be able to propagate them itself.
    fn log_learned(&mut self, c: &[u32]) {
        if self.proof.is_none() { return; }
        self.proof_sync();
        if let Some(p) = &mut self.proof { p.add(c); }
    }

    /// Derive the box reasons of the level-0 trail entries added since the
    /// last call.  Cheap once caught up: the level-0 trail only grows.
    fn proof_sync(&mut self) {
        if self.proof.is_none() || !self.trail_lim.is_empty() { return; }
        while self.proof_l0 < self.trail.len() {
            let v = self.trail[self.proof_l0];
            self.proof_l0 += 1;
            if matches!(self.reason[v as usize], Reason::Box(_)) {
                let mut out = Vec::new();
                self.reason_lits(v, &mut out);   // justifies the lemma as a side effect
            }
        }
    }

    /// Emit the clause `lemma` (a box reason or a box conflict, as literal
    /// codes) with a derivation from the box source clauses.  A lemma the
    /// sub-engine cannot refute marks the proof incomplete.
    fn justify_box(&mut self, lemma: &[u32]) {
        if self.proof.is_none() { return; }
        let mut key: Vec<u32> = lemma.to_vec();
        key.sort_unstable(); key.dedup();
        if !self.lemma_seen.insert(key) { return; }
        if self.justifier.is_none() {
            if self.box_src.is_empty() {
                if let Some(p) = &mut self.proof {
                    p.fail("a box propagated and no source clauses were given (--boxes-source)");
                }
                return;
            }
            let src = std::mem::take(&mut self.box_src);
            let mut j = Box::new(Engine::from_cnf(self.nvars, &src));
            self.box_src = src;
            j.proof = Some(proof::Proof::buffer());
            j.init();
            self.justifier = Some(j);
        }
        let mut j = self.justifier.take().expect("justifier built above");
        // ¬lemma: every literal of the lemma false
        let units: Vec<Lit> = lemma.iter().map(|&l| Lit { var: l >> 1, neg: (l & 1) == 0 }).collect();
        let verdict = j.solve_under(&units);
        let steps = j.proof.as_mut().map(|p| p.take_buffer()).unwrap_or_default();
        self.justifier = Some(j);
        match verdict {
            Verdict::Unsat => {
                if let Some(p) = &mut self.proof {
                    p.lemmas += 1;
                    p.lemma_steps += steps.len() as u64;
                    for d in &steps { if d.is_empty() { p.empty(); } else { p.add_dimacs(d); } }
                    p.add(lemma);
                }
            }
            _ => {
                let show: Vec<i32> = lemma.iter().map(|&l| { let v = (l >> 1) as i32 + 1; if l & 1 == 1 { -v } else { v } }).collect();
                if let Some(p) = &mut self.proof {
                    p.fail(format!("a box lemma does not follow from the source clauses: {show:?}"));
                }
            }
        }
    }

    fn grow(&mut self, nvars: usize) {
        if nvars <= self.nvars { return; }
        self.nvars = nvars;
        // The box occurrence lists, the explanation cache and the explain-
        // clause index exist only once something uses them (add_box,
        // add_explain_clause); on a plain CNF each was a 24-byte empty
        // header per variable or literal -- 700 MB at 7.3 M variables, and
        // 22 GB at the 117 M of the instance that started the memory work.
        if !self.occ.is_empty() { self.occ.resize(nvars, Vec::new()); }
        self.vals.resize(nvars, Val::U);
        self.level.resize(nvars, 0);
        self.reason.resize(nvars, Reason::None);
        self.trail_pos.resize(nvars, 0);
        self.activity.resize(nvars, 0.0);
        self.phase.resize(nvars, false);
        self.seen.resize(nvars, false);
        self.shrink_mark.resize(nvars, false);
        self.watches.resize(2 * nvars);
        self.bins.resize(2 * nvars);
        if !self.xidx.is_empty() { self.xidx.resize(2 * nvars, Vec::new()); }
        self.lvals.resize(2 * nvars, Val::U);
        if !self.expl_cache.is_empty() { self.expl_cache.resize_with(nvars, Vec::new); }
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
    /// Turn the branching-heuristic study on or off before solving
    /// (`BOXES_EFF_STUDY=1` does it at construction, which is the usual
    /// route).  Recomputes the live counts from the masks, because turning
    /// it on after unit clauses have already killed rows at level 0 would
    /// otherwise leave every count at the value it had when its box was
    /// added.
    pub fn set_eff_study(&mut self, on: bool) {
        assert_eq!(self.decision_level(), 0, "the study is switched before solving");
        self.eff_study = on;
        self.snap_count.clear();
        self.live_count.clear();
        self.eff_box_hits.clear();
        self.eff_clause_hits.clear();
        if on {
            for h in &self.hdr {
                let (off, nw) = (h.off as usize, h.nw as usize);
                self.live_count.push((0..nw).map(|w| self.live[off + w].count_ones()).sum());
            }
            self.eff_box_hits.resize(self.hdr.len(), 0);
        }
    }

    /// The clauses carrying the most conflicts, most first — the mining
    /// seed described on [`EffClause`].
    ///
    /// Counts are keyed by clause index and reset whenever `simplify`
    /// renumbers the store, so this covers the run since the last rebuild.
    pub fn eff_clause_dump(&self, top: usize) -> Vec<EffClause> {
        let mut out: Vec<EffClause> = (0..self.eff_clause_hits.len().min(self.cstart.len()))
            .filter(|&ci| self.eff_clause_hits[ci] > 0)
            .map(|ci| {
                let learned = ci >= self.first_learnt;
                let k = ci.wrapping_sub(self.first_learnt);
                EffClause {
                    lits: self.clause(ci).iter().map(|&l| {
                        let v = (l >> 1) as i32 + 1;
                        if l & 1 == 1 { -v } else { v }
                    }).collect(),
                    conflicts: self.eff_clause_hits[ci],
                    learned,
                    lbd: if learned { self.learnt_lbd.get(k).copied().unwrap_or(0) } else { 0 },
                    activity: if learned { self.learnt_act.get(k).copied().unwrap_or(0.0) } else { 0.0 },
                    deleted: self.deleted.get(ci).copied().unwrap_or(false),
                }
            })
            .collect();
        out.sort_unstable_by(|a, b| b.conflicts.cmp(&a.conflicts));
        out.truncate(top);
        out
    }

    /// Conflicts per box, in box order — empty unless the study is on.
    /// Boxes appended to a `--boxes` set land at the end, so a mined box's
    /// share of the failures is the tail of this.
    pub fn eff_box_hits(&self) -> &[u32] { &self.eff_box_hits }

    /// How concentrated the table conflicts are: the share carried by the
    /// busiest 1% and 10% of boxes, and how many boxes failed at all out of
    /// how many.
    ///
    /// Mining a benchmark for structure worth compiling only pays if the
    /// failures concentrate — if every box fails about equally often there
    /// is no "powerful box" to find, only a uniform cost of doing business.
    pub fn eff_concentration(&self) -> Option<(f64, f64, usize, usize)> {
        if !self.eff_study || self.eff_box_hits.is_empty() { return None; }
        let mut v = self.eff_box_hits.clone();
        v.sort_unstable_by(|a, b| b.cmp(a));
        let total: u64 = v.iter().map(|&x| x as u64).sum();
        if total == 0 { return None; }
        let share = |k: usize| v.iter().take(k.max(1)).map(|&x| x as u64).sum::<u64>() as f64 / total as f64;
        let hit = v.iter().filter(|&&x| x > 0).count();
        Some((share(v.len() / 100), share(v.len() / 10), hit, v.len()))
    }

    /// `BOXES_MEM_REPORT=1`: the process's peak RSS so far and the retained
    /// size of each structure, at a named point.  Exists because flattening
    /// the parser's clause list moved peak memory by only 6-11 % on large
    /// instances (2026-09-21): the rest is in here, and which structure it
    /// is was a guess until this printed it.  A jump in peak RSS between
    /// two reports with no matching growth in the table is a transient —
    /// level-0 simplification builds and drops its own copies.
    /// A bare peak-RSS checkpoint, for points inside a routine where the
    /// retained table would say nothing about the transients that are the
    /// question.  Peak RSS is monotonic, so the first checkpoint at which
    /// it rises is where the peak is.
    fn mem_mark(&self, label: &str) {
        if matches!(std::env::var("BOXES_MEM_REPORT").as_deref(), Ok("1") | Ok("on")) {
            let (used, free) = malloc_stats();
            eprintln!("c boxes: mem [{}]: peak RSS {:.0} MB, footprint now {:.0} MB (malloc: {:.0} live, {:.0} freed-and-kept)",
                      label, peak_rss_bytes() as f64 / 1e6, cur_footprint_bytes() as f64 / 1e6, used as f64 / 1e6, free as f64 / 1e6);
        }
    }

    pub fn mem_report(&self, label: &str) {
        if !matches!(std::env::var("BOXES_MEM_REPORT").as_deref(), Ok("1") | Ok("on")) { return; }
        // (label, capacity bytes, bytes in use): the gap is doubling slack,
        // resident wherever a buffer has been copied into (always, for the
        // small per-literal vectors; only up to the copy for a large one).
        let mut rows: Vec<(String, usize, usize)> = Vec::new();
        macro_rules! flat { ($($f:ident),*) => { $( rows.push((stringify!($f).to_string(), vec_cap_bytes(&self.$f), vec_bytes(&self.$f))); )* } }
        macro_rules! nested { ($($f:ident),*) => { $( { let (b, n) = vecvec_bytes(&self.$f);
            let used = n * 24 + self.$f.iter().map(|v| vec_bytes(v)).sum::<usize>();
            rows.push((format!("{} ({} inner vecs = {:.0} MB of headers)", stringify!($f), n, n as f64 * 24.0 / 1e6), b, used)); } )* } }
        flat!(arena, cstart, clen, xarena, xstart, xlen, learnt_lbd, learnt_act, learnt_used, deleted,
              vals, lvals, level, reason, trail_pos, trail, activity, phase, seen, heap, heap_pos,
              target_phase, best_phase, eliminated, expl_ok, hdr, vars_all, kill_all, live, snap,
              in_queue, queue, lbd_stamp, live_count, snap_count);
        nested!(occ, xidx, expl_cache, box_src);
        for (name, ls) in [("watches", &self.watches), ("bins", &self.bins)] {
            rows.push((format!("{} (flat: {} lists = {:.0} MB of headers, {:.0} MB of holes)", name, ls.n(),
                               ls.n() as f64 * 12.0 / 1e6, ls.holes as f64 * 8.0 / 1e6), ls.cap_bytes(), ls.used_bytes()));
        }
        rows.push((format!("elim ({} eliminated vars' clauses)", self.elim.len()), self.elim.cap_bytes(), self.elim.used_bytes()));
        rows.sort_by(|a, b| b.1.cmp(&a.1));
        let total: usize = rows.iter().map(|r| r.1).sum();
        let used: usize = rows.iter().map(|r| r.2).sum();
        let (mused, mfree) = malloc_stats();
        eprintln!("c boxes: mem [{}]: peak RSS {:.0} MB, footprint now {:.0} MB (malloc: {:.0} live, {:.0} freed-and-kept); engine structures hold {:.0} MB of capacity, {:.0} in use, largest:",
                  label, peak_rss_bytes() as f64 / 1e6, cur_footprint_bytes() as f64 / 1e6, mused as f64 / 1e6, mfree as f64 / 1e6, total as f64 / 1e6, used as f64 / 1e6);
        for (n, b, u) in rows.iter().take(10) {
            if *b == 0 { continue; }
            if *u < *b / 20 * 19 { eprintln!("c boxes: mem   {:>8.0} MB  {} ({:.0} in use)", *b as f64 / 1e6, n, *u as f64 / 1e6); }
            else { eprintln!("c boxes: mem   {:>8.0} MB  {}", *b as f64 / 1e6, n); }
        }
    }

    pub fn add_box(&mut self, b: TableBox) {
        let bi = self.hdr.len() as u32;
        let nw = b.nwords as u32;
        let (vbase, kbase) = (self.vars_all.len() as u32, self.kill_all.len() as u32);
        if let Some(&max) = b.vars.iter().max() { self.grow(max as usize + 1); }
        // First box: the per-variable tables come into existence now, sized
        // to the variables so far; `grow` keeps them in step from here on.
        if self.occ.len() < self.nvars { self.occ.resize(self.nvars, Vec::new()); }
        if self.expl_cache.len() < self.nvars { self.expl_cache.resize_with(self.nvars, Vec::new); }
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
        if self.eff_study {
            self.live_count.push((0..nw).map(|w| self.live[off + w].count_ones()).sum());
            self.eff_box_hits.push(0);
        }
        self.in_queue.push(false);
    }

    /// Add a clause (before solving).  Tautologies are dropped, duplicate
    /// literals merged; the empty clause makes the engine unsatisfiable, a
    /// unit clause is a level-0 assignment.
    pub fn add_clause(&mut self, lits: &[Lit]) { self.add_clause_impl(lits, true) }

    /// `add_clause` with the watches left for
    /// [`attach_watches`](Self::attach_watches) when `attach` is false: a
    /// bulk load can then size every watch list exactly, and a rebuild can
    /// drop its source before the watch lists exist.
    fn add_clause_impl(&mut self, lits: &[Lit], attach: bool) {
        if let Some(max) = lits.iter().map(|l| l.var).max() { self.grow(max as usize + 1); }
        let mut c: Vec<u32> = lits.iter().map(|l| code(l.var, l.neg)).collect();
        c.sort_unstable(); c.dedup();
        if c.windows(2).any(|w| w[0] >> 1 == w[1] >> 1) { return; }   // x ∨ ¬x
        if let Some(p) = &mut self.proof { p.add(&c); }   // a resolvent; the input clauses precede the sink
        match c.len() {
            0 => self.unsat_at_init = true,
            1 => { let l = c[0]; if !self.assign(l >> 1, if l & 1 == 1 { Val::F } else { Val::T }, Reason::None) { self.unsat_at_init = true; } }
            _ => {
                let ci = self.cstart.len() as u32;
                if attach {
                    if c.len() == 2 {
                        self.bins.push(c[0] as usize, (c[1], ci));
                        self.bins.push(c[1] as usize, (c[0], ci));
                    } else {
                        self.watches.push(c[0] as usize, (ci, c[1]));
                        self.watches.push(c[1] as usize, (ci, c[0]));
                    }
                }
                self.push_clause(&c);
                self.deleted.push(false);
                self.first_learnt = self.cstart.len();
            }
        }
    }

    /// Add an explanation-only clause (before solving): never propagated,
    /// only offered as the reason for a literal a table forces.
    pub fn add_explain_clause(&mut self, lits: &[Lit]) {
        if let Some(max) = lits.iter().map(|l| l.var).max() { self.grow(max as usize + 1); }
        let mut c: Vec<u32> = lits.iter().map(|l| code(l.var, l.neg)).collect();
        c.sort_unstable(); c.dedup();
        if c.len() < 2 || c.windows(2).any(|w| w[0] >> 1 == w[1] >> 1) { return; }
        let xi = self.xstart.len() as u32;
        self.xstart.push(self.xarena.len() as u32);
        self.xlen.push(c.len() as u32);
        if self.xidx.len() < 2 * self.nvars { self.xidx.resize(2 * self.nvars, Vec::new()); }
        for &l in &c { self.xidx[l as usize].push(xi); }
        self.xarena.extend_from_slice(&c);
    }

    pub fn nexplain(&self) -> usize { self.xstart.len() }

    pub fn nvars(&self) -> usize { self.nvars }
    pub fn nboxes(&self) -> usize { self.hdr.len() }
    pub fn nclauses(&self) -> usize { self.cstart.len() }

    #[inline] fn clause(&self, ci: usize) -> &[u32] {
        let s = self.cstart[ci] as usize;
        &self.arena[s..s + self.clen[ci] as usize]
    }

    /// Watch clauses `from..to` of the store on their first two literals,
    /// in index order -- exactly what `add_clause` does as each arrives --
    /// after a counting pass sizes every per-literal list, so a bulk load
    /// neither doubles its way up (millions of small reallocations) nor
    /// keeps the slack.  Per-literal order is unchanged: increasing clause
    /// index either way, so propagation visits the same clauses in the same
    /// order and the search is identical.
    fn attach_watches(&mut self, from: usize, to: usize) {
        let nl = self.watches.n();
        let (mut cw, mut cb) = (vec![0u32; nl], vec![0u32; nl]);
        for ci in from..to {
            if self.deleted[ci] { continue; }
            let st = self.cstart[ci] as usize;
            let (a, b) = (self.arena[st] as usize, self.arena[st + 1] as usize);
            let cnt = if self.clen[ci] == 2 { &mut cb } else { &mut cw };
            cnt[a] += 1; cnt[b] += 1;
        }
        self.watches.layout_exact(&cw);
        self.bins.layout_exact(&cb);
        drop(cw); drop(cb);
        for ci in from..to {
            if self.deleted[ci] { continue; }
            let st = self.cstart[ci] as usize;
            let (a, b) = (self.arena[st], self.arena[st + 1]);
            if self.clen[ci] == 2 {
                self.bins.push(a as usize, (b, ci as u32));
                self.bins.push(b as usize, (a, ci as u32));
            } else {
                self.watches.push(a as usize, (ci as u32, b));
                self.watches.push(b as usize, (ci as u32, a));
            }
        }
    }

    fn push_clause(&mut self, lits: &[u32]) -> usize {
        let ci = self.cstart.len();
        self.cstart.push(self.arena.len() as u32);
        self.clen.push(lits.len() as u32);
        self.arena.extend_from_slice(lits);
        ci
    }

    fn delete_clause(&mut self, ci: usize) {
        if self.proof.is_some() {
            let lits = self.clause(ci).to_vec();
            if let Some(p) = &mut self.proof { p.del(&lits); }
        }
        self.deleted[ci] = true; self.clen[ci] = 0;
    }

    /// Drop the deleted clauses' literals; indices stay, offsets move.
    fn compact_arena(&mut self) {
        // Only the learned tail moves, and in place: storage is monotone
        // in clause index (push_clause appends, compaction keeps the
        // order), so a clause only ever moves left.  The originals stay
        // where they are -- a subsumed original's slack is bounded by the
        // input, while copying the whole store into a fresh arena on every
        // reduction was 15 x 561 MB on the 40 M-clause instance, with the
        // freed arena staying charged: 2 GB of the search's peak RSS
        // (2026-09-21, doc/data/boxes_memory_2026-09-20.txt s10).
        let mut w = if self.first_learnt < self.cstart.len() { self.cstart[self.first_learnt] as usize } else { self.arena.len() };
        for ci in self.first_learnt..self.cstart.len() {
            let (s, n) = (self.cstart[ci] as usize, self.clen[ci] as usize);
            debug_assert!(s >= w, "clause storage not monotone in clause index");
            if n > 0 && s != w { self.arena.copy_within(s..s + n, w); }
            self.cstart[ci] = w as u32;
            w += n;
        }
        self.arena.truncate(w);
    }
    fn decision_level(&self) -> usize { self.trail_lim.len() }

    #[inline] fn lit_value(&self, c: u32) -> Val { self.lvals[c as usize] }

    fn new_level(&mut self) {
        self.trail_lim.push(self.trail.len());
        self.snap.extend_from_slice(&self.live);
        if self.eff_study { self.snap_count.extend_from_slice(&self.live_count); }
    }

    /// Undo decision levels above `lvl`.
    fn backjump(&mut self, lvl: usize) {
        if self.decision_level() <= lvl { return; }
        let t = self.trail_lim[lvl];
        let mut kept = std::mem::take(&mut self.chrono_kept_scratch);
        kept.clear();
        while self.trail.len() > t {
            let v = self.trail.pop().unwrap() as usize;
            if self.chrono && self.level[v] as usize <= lvl { kept.push(v as u32); continue; }
            self.phase[v] = self.vals[v] == Val::T;
            self.vals[v] = Val::U;
            self.lvals[2 * v] = Val::U;
            self.lvals[2 * v + 1] = Val::U;
            self.reason[v] = Reason::None;
            self.expl_ok[v] = false;
            self.heap_insert(v as u32);
        }
        let n = self.live.len();
        let start = self.trail_lim.len() - lvl;   // levels popped
        let from = self.snap.len() - start * n;
        self.live.copy_from_slice(&self.snap[from..from + n]);
        self.snap.truncate(from);
        if self.eff_study {
            let nc = self.live_count.len();
            let fromc = self.snap_count.len() - start * nc;
            self.live_count.copy_from_slice(&self.snap_count[fromc..fromc + nc]);
            self.snap_count.truncate(fromc);
        }
        self.trail_lim.truncate(lvl);
        self.clear_queue();
        // The kept literals go back on in their original order, so each still
        // follows everything that implied it.  The snapshot restored above
        // predates them, so their kills are re-applied (which re-queues the
        // boxes they touch).  And they are propagated again: propagation stops
        // at the first conflict, so a kept literal may never have been
        // propagated at all, and skipping it leaves its consequences — a
        // binary clause against another kept literal, say — underived for
        // good.  (Measured: PHP-9-8 with backtracking forced chronological
        // returned a model violating a binary clause, which the model
        // self-check refused.)  Without chronological mode nothing is kept and
        // this is the usual `qhead = trail.len()`.
        for &v in kept.iter().rev() {
            self.trail_pos[v as usize] = self.trail.len() as u32;
            self.trail.push(v);
            let val = self.vals[v as usize];
            self.apply_kills(v as usize, val);
        }
        self.stats.chrono_kept += kept.len() as u64;
        self.chrono_kept_scratch = kept;
        self.qhead = t;
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
        self.lvals[2 * v] = val;
        self.lvals[2 * v + 1] = if val == Val::T { Val::F } else { Val::T };
        self.level[v] = match reason {
            // chronological mode: an implied literal lives at the highest level
            // of the literals that imply it, so a later backjump to any level
            // at or above that keeps it.  A table reason keeps the current
            // level — computing its explanation here would undo the laziness
            // that makes boxes cheap, and a level that is too high is sound
            // (the literal is just unassigned more eagerly).
            Reason::Clause(ci) if self.chrono && !self.trail_lim.is_empty() => {
                let mut m = 0u32;
                for &l in self.clause(ci as usize) { let u = (l >> 1) as usize; if u != v && self.level[u] > m { m = self.level[u]; } }
                m
            }
            _ => self.decision_level() as u32,
        };
        self.reason[v] = reason;
        self.trail_pos[v] = self.trail.len() as u32;
        self.trail.push(var);
        self.apply_kills(v, val);
        true
    }

    /// Remove from every box the rows `v = val` kills, queueing the boxes that
    /// changed.
    fn apply_kills(&mut self, v: usize, val: Val) {
        if self.occ.is_empty() { return; }   // no boxes: nothing to kill
        for k in 0..self.occ[v].len() {
            let Occ { b, koff } = self.occ[v][k];
            let h = self.hdr[b as usize];
            let (off, nw) = (h.off as usize, h.nw as usize);
            let kb = koff as usize + if val == Val::T { nw } else { 0 };
            let (mut changed, mut removed) = (false, 0u32);
            for w in 0..nw {
                let old = self.live[off + w];
                let new = old & !self.kill_all[kb + w];
                if new != old {
                    self.live[off + w] = new;
                    changed = true;
                    if self.eff_study { removed += (old & !new).count_ones(); }
                }
            }
            if self.eff_study { self.live_count[b as usize] -= removed; }
            if changed && !self.in_queue[b as usize] { self.in_queue[b as usize] = true; self.queue.push(b); }
        }
    }

    /// Propagate to fixpoint: clauses through the trail (two watched
    /// literals), tables through the queue of boxes whose live rows shrank.
    fn propagate(&mut self) -> Option<Conflict> {
        let count = self.count_visits;
        loop {
            while self.qhead < self.trail.len() {
                let v = self.trail[self.qhead];
                self.qhead += 1;
                if self.qhead & 4095 == 0 && let Some(c) = &self.cancel && c.load(std::sync::atomic::Ordering::Relaxed) {
                    self.cancelled = true;
                    return None;
                }
                let false_lit = code(v, self.vals[v as usize] == Val::T);   // the literal made FALSE
                // binary clauses: no clause memory touched
                for k in self.bins.range(false_lit as usize) {
                    let (other, ci) = self.bins.data[k];
                    if count { self.stats.bin_visits += 1; }
                    match self.lvals[other as usize] {
                        Val::T => {}
                        Val::F => { self.clear_queue(); return Some(Conflict::Clause(ci)); }
                        Val::U => {
                            self.stats.propagations += 1;
                            self.assign(other >> 1, if other & 1 == 1 { Val::F } else { Val::T }, Reason::Clause(ci));
                        }
                    }
                }
                // The list is compacted in its own slot; a new watch pushed
                // onto another literal's list can move THAT list to the end
                // of the arena, never this one (the new watch is not false,
                // so it is not `false_lit`).
                let s0 = self.watches.start[false_lit as usize] as usize;
                let n0 = self.watches.len[false_lit as usize] as usize;
                let mut i = 0;
                let mut j = 0;
                let mut conflict = None;
                while i < n0 {
                    let (ci, blocker) = self.watches.data[s0 + i];
                    i += 1;
                    if count { self.stats.watch_visits += 1; }
                    if self.deleted[ci as usize] { continue; }
                    // A true blocker lets a false watch skip the clause only if a
                    // backtrack that unassigns the blocker must unassign the
                    // watch too: in chronological mode that needs the blocker's
                    // level to be no higher than the watch's.  Otherwise both
                    // watches could stay false above an unassigned literal and a
                    // later conflict on it would go unseen.
                    if self.lvals[blocker as usize] == Val::T
                        && (!self.chrono || self.level[(blocker >> 1) as usize] <= self.level[(false_lit >> 1) as usize]) {
                        if count { self.stats.blocker_hits += 1; }
                        self.watches.data[s0 + j] = (ci, blocker); j += 1; continue;
                    }
                    let s = self.cstart[ci as usize] as usize;
                    let len = self.clen[ci as usize] as usize;
                    if count { self.stats.clause_visits += 1; }
                    if self.arena[s] == false_lit { self.arena.swap(s, s + 1); }
                    let other = self.arena[s];
                    if other != blocker && self.lvals[other as usize] == Val::T { self.watches.data[s0 + j] = (ci, other); j += 1; continue; }
                    // a new watch: any literal not false
                    let mut found = false;
                    for k in 2..len {
                        let l = self.arena[s + k];
                        if count { self.stats.lit_steps += 1; }
                        if self.lvals[l as usize] != Val::F {
                            self.arena.swap(s + 1, s + k);
                            self.watches.push(l as usize, (ci, other));
                            found = true;
                            break;
                        }
                    }
                    if found { continue; }
                    // No replacement: the clause is unit on `other` or false.  In
                    // chronological mode the false watch must be the literal of
                    // highest level, so that any backtrack that unassigns a
                    // literal of the clause also unassigns this watch.
                    let mut moved = false;
                    if self.chrono && len > 2 {
                        let mut best = s + 1;
                        let mut bl = self.level[(self.arena[s + 1] >> 1) as usize];
                        for k in 2..len {
                            let lv = self.level[(self.arena[s + k] >> 1) as usize];
                            if lv > bl { best = s + k; bl = lv; }
                        }
                        if best != s + 1 {
                            self.arena.swap(s + 1, best);
                            let nl = self.arena[s + 1];
                            self.watches.push(nl as usize, (ci, other));
                            moved = true;
                        }
                    }
                    if !moved { self.watches.data[s0 + j] = (ci, other); j += 1; }
                    if self.lvals[other as usize] == Val::F {
                        conflict = Some(Conflict::Clause(ci));
                        while i < n0 { self.watches.data[s0 + j] = self.watches.data[s0 + i]; i += 1; j += 1; }
                        break;
                    }
                    self.stats.propagations += 1;
                    self.assign(other >> 1, if other & 1 == 1 { Val::F } else { Val::T }, Reason::Clause(ci));
                }
                self.watches.len[false_lit as usize] = j as u32;
                if let Some(c) = conflict { self.clear_queue(); return Some(c); }
            }
            let b = self.queue.pop()?;
            let b = b as usize;
            self.in_queue[b] = false;
            let h = self.hdr[b];
            let (off, nw) = (h.off as usize, h.nw as usize);
            debug_assert!(!self.eff_study || self.live_count[b] == (0..nw).map(|w| self.live[off + w].count_ones()).sum::<u32>(),
                          "live_count out of step with live for box {b}");
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

    /// Record where the conflicting box ranked by live rows at the
    /// preceding decision — see [`EffStudy`].  Called before the conflict
    /// is analysed, while the top snapshot is still that decision's.
    fn eff_sample(&mut self, conflict: Conflict) {
        let b = match conflict {
            Conflict::Clause(ci) => {
                self.stats.eff.clause_conflicts += 1;
                if ci as usize >= self.first_learnt { self.stats.eff.clause_conflicts_learned += 1; }
                if self.eff_study {
                    if self.eff_clause_hits.len() <= ci as usize { self.eff_clause_hits.resize(ci as usize + 1, 0); }
                    self.eff_clause_hits[ci as usize] += 1;
                }
                return;
            }
            Conflict::Box(b) | Conflict::Forced { b, .. } => b as usize,
        };
        self.stats.eff.box_conflicts += 1;
        if !self.eff_study { return; }
        self.eff_box_hits[b] += 1;
        let n = self.live_count.len();
        if n == 0 || self.trail_lim.is_empty() { self.stats.eff.unsampled += 1; return; }
        let at = &self.snap_count[self.snap_count.len() - n..];
        let size = |i: usize| self.hdr[i].nrows.max(1) as f64;
        let mine = at[b];
        let mine_frac = mine as f64 / size(b);
        let (mut less, mut equal, mut total) = (0usize, 0usize, 0u64);
        let (mut less_f, mut equal_f) = (0usize, 0usize);
        let (mut total_f, mut total_n) = (0.0f64, 0u64);
        for (i, &x) in at.iter().enumerate() {
            if x < mine { less += 1 } else if x == mine { equal += 1 }
            total += x as u64;
            let f = x as f64 / size(i);
            if f < mine_frac { less_f += 1 } else if f == mine_frac { equal_f += 1 }
            total_f += f;
            total_n += self.hdr[i].nrows as u64;
        }
        // Mid-rank within the tied block, so a population of equal counts
        // lands mid-scale instead of pretending to be most constrained.
        let rank = less as f64 + (equal as f64 - 1.0) / 2.0;
        let rank_f = less_f as f64 + (equal_f as f64 - 1.0) / 2.0;
        let nrows = self.hdr[b].nrows;
        let e = &mut self.stats.eff;
        e.sampled += 1;
        e.deciles[((rank / n as f64) * 10.0) as usize % 10] += 1;
        if less == 0 { e.top1 += 1; }
        if less < 10 { e.top10 += 1; }
        e.conflict_rows += mine as u64;
        e.population_rows += total as f64 / n as f64;
        e.deciles_frac[((rank_f / n as f64) * 10.0) as usize % 10] += 1;
        if less_f == 0 { e.top1_frac += 1; }
        e.conflict_frac += mine_frac;
        e.population_frac += total_f / n as f64;
        e.conflict_nrows += nrows as u64;
        e.population_nrows += total_n as f64 / n as f64;
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
            Reason::Clause(ci) => for &l in self.clause(ci as usize) { if l >> 1 != var { out.push(l); } },
            Reason::Box(b) => {
                if self.expl_ok[var as usize] {
                    self.stats.explanation_hits += 1;
                    out.extend_from_slice(&self.expl_cache[var as usize]);
                    return;
                }
                let start = out.len();
                // a gate clause of the cone, unit for this literal under the
                // assignment that preceded it, is a shorter reason than the cover
                let t = code(var, self.vals[var as usize] == Val::F);   // the TRUE literal of var
                let pos = self.trail_pos[var as usize];
                let mut found = false;
                for k in 0..self.xidx.get(t as usize).map_or(0, |x| x.len()) {
                    let xi = self.xidx[t as usize][k] as usize;
                    let (s, n) = (self.xstart[xi] as usize, self.xlen[xi] as usize);
                    let unit = (0..n).all(|j| { let l = self.xarena[s + j]; l == t || (self.lvals[l as usize] == Val::F && self.trail_pos[(l >> 1) as usize] < pos) });
                    if unit {
                        for j in 0..n { let l = self.xarena[s + j]; if l != t { out.push(l); } }
                        self.stats.explanation_gate += 1;
                        found = true;
                        break;
                    }
                }
                if !found {
                    let li = self.local_index(b, var);
                    let val = self.vals[var as usize] == Val::T;
                    let mut target = self.rows_mask(b, Some((li, val)));
                    self.explain_box(b, &mut target, self.trail_pos[var as usize] as usize, out);
                }
                let mut cache = std::mem::take(&mut self.expl_cache[var as usize]);
                cache.clear();
                cache.extend_from_slice(&out[start..]);
                self.expl_cache[var as usize] = cache;
                self.expl_ok[var as usize] = true;
                if self.proof.is_some() {
                    let mut lemma: Vec<u32> = out[start..].to_vec();
                    lemma.push(t);
                    self.justify_box(&lemma);
                }
            }
        }
    }

    /// The false literals of a conflict.
    fn conflict_lits(&mut self, conflict: Conflict, out: &mut Vec<u32>) {
        match conflict {
            Conflict::Clause(ci) => out.extend_from_slice(self.clause(ci as usize)),
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
        if self.used_grace { self.learnt_used[k] = MAX_USED; }
        // A clause's LBD is not a constant: the trail it was learned from
        // is gone, and the levels its literals sit at now may be fewer.
        // Recomputing on use lets a clause earn its way into a better tier
        // instead of being judged once, at birth.  LBD 0 is the permanence
        // marker, never a real LBD, so it is left alone.
        if self.promote && self.learnt_lbd[k] != 0 {
            let g = self.recompute_lbd(ci as usize);
            if g < self.learnt_lbd[k] {
                self.learnt_lbd[k] = g;
                self.learnt_used[k] = MAX_USED;
                self.stats.promoted += 1;
            }
        }
    }

    /// The LBD of clause `ci` under the *current* trail, without
    /// allocating: a generation-stamped array over levels, so nothing has
    /// to be cleared between calls.
    fn recompute_lbd(&mut self, ci: usize) -> u32 {
        let (start, len) = (self.cstart[ci] as usize, self.clen[ci] as usize);
        self.lbd_gen += 1;
        let (stamp, mut g) = (self.lbd_gen, 0u32);
        for i in 0..len {
            let lv = self.level[(self.arena[start + i] >> 1) as usize] as usize;
            if self.lbd_stamp.len() <= lv { self.lbd_stamp.resize(lv + 1, 0); }
            if self.lbd_stamp[lv] != stamp { self.lbd_stamp[lv] = stamp; g += 1; }
        }
        g.max(1)
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
        let n = self.cstart.len() - self.first_learnt;
        // A clause that is the reason for its first literal is still needed.
        let is_reason = |e: &Engine, ci: usize| {
            let l0 = e.clause(ci)[0];
            e.reason[(l0 >> 1) as usize] == Reason::Clause(ci as u32) && e.vals[(l0 >> 1) as usize] != Val::U
        };
        // LBD 0 is not a real LBD (it counts distinct levels, so it is at
        // least 1): it marks a clause promoted by subsumption, standing in
        // for an original clause that was deleted.  Dropping one would lose
        // a constraint of the input formula.
        let mut order: Vec<usize>;
        let drop;
        if self.used_grace {
            // CaDiCaL's rule, ported: decay every clause's `used` once per
            // reduction, then spare a tier-1 clause that has been resolved
            // within the last `MAX_USED` reductions, and a tier-2 clause
            // only if analysis resolved it since the previous reduction.
            // What is left is the candidate set, and a fixed percentage of
            // *that* is dropped — not a fraction of the whole database,
            // which is a different and much blunter pool.
            order = Vec::with_capacity(n);
            for k in 0..n {
                let ci = self.first_learnt + k;
                if self.deleted[ci] || self.learnt_lbd[k] == 0 || self.clen[ci] <= 2 { continue; }
                if is_reason(self, ci) { continue; }
                let used = self.learnt_used[k];
                if used > 0 { self.learnt_used[k] = used - 1; }
                if self.learnt_lbd[k] <= self.keep_lbd && used > 0 { self.stats.spared += 1; continue; }
                if self.learnt_lbd[k] <= self.tier2_lbd && used + 1 >= MAX_USED { self.stats.spared += 1; continue; }
                order.push(k);
            }
            drop = order.len() * self.reduce_target.min(100) / 100;
        } else {
            order = (0..n).filter(|&k| !self.deleted[self.first_learnt + k]).collect();
            drop = order.len() / self.reduce_frac.max(1);
        }
        order.sort_by(|&a, &b| self.learnt_lbd[b].cmp(&self.learnt_lbd[a])
            .then(self.learnt_act[a].partial_cmp(&self.learnt_act[b]).unwrap_or(std::cmp::Ordering::Equal)));
        let mut removed = 0usize;
        for &k in order.iter().take(drop) {
            if !self.used_grace && (self.learnt_lbd[k] == 0 || self.learnt_lbd[k] <= self.keep_lbd) { continue; }
            let ci = self.first_learnt + k;
            if !self.used_grace && self.clen[ci] <= 2 { continue; }
            if !self.used_grace && is_reason(self, ci) { continue; }
            self.delete_clause(ci);
            removed += 1;
        }
        self.stats.deleted += removed as u64;
        self.stats.reductions += 1;
        self.compact_arena();
        // Reclaim the holes relocated watch lists left; the search holds
        // no index into the arenas here.
        self.watches.defrag();
        self.bins.defrag();
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
    /// Shrink one level block of a learned clause (Fleury and Biere, "Efficient
    /// All-UIP Learned Clause Minimization", SAT 2021): the clause's literals
    /// at `lvl`, all false, are replaced by a single literal at `lvl` that
    /// implies them — the block's UIP.  Walk the block's literals from the
    /// highest trail position down, resolving each with its reason; a reason
    /// literal at `lvl` joins the walk, one at a lower level must already be
    /// in the clause (`seen`) or be redundant by minimisation, anything else
    /// abandons the block.  When one literal is left open it dominates the
    /// whole block.  The walk cannot run out: the level's decision has the
    /// lowest trail position of any literal at `lvl`, so it is always the
    /// last one open.  Returns the UIP's variable on success.
    ///
    /// The shrunk clause stays RUP: setting the UIP to its trail value
    /// re-derives every literal of the block through the reasons the walk
    /// resolved on, whose lower-level literals are in the clause or implied
    /// by it — so the certified path needs nothing new.
    fn shrink_block(&mut self, lvl: u32, block: &[u32], levels: u32) -> Option<u32> {
        use std::collections::BinaryHeap;
        self.stats.shrink_tried += 1;
        let mut heap: BinaryHeap<(u32, u32)> = BinaryHeap::with_capacity(2 * block.len());
        let mut marked: Vec<u32> = Vec::with_capacity(2 * block.len());
        for &v in block {
            self.shrink_mark[v as usize] = true;
            marked.push(v);
            heap.push((self.trail_pos[v as usize], v));
        }
        let mut open = block.len();
        let mut lits: Vec<u32> = Vec::new();
        let mut uip = None;
        'walk: while let Some((_, v)) = heap.pop() {
            if open == 1 { uip = Some(v); break; }
            if self.reason[v as usize] == Reason::None { break; }   // cannot happen with open > 1; be safe
            lits.clear();
            self.reason_lits(v, &mut lits);
            for i in 0..lits.len() {
                let u = (lits[i] >> 1) as usize;
                let lu = self.level[u];
                if lu == 0 { continue; }
                if lu == lvl {
                    if !self.shrink_mark[u] { self.shrink_mark[u] = true; marked.push(u as u32); heap.push((self.trail_pos[u], u as u32)); open += 1; }
                } else if lu < lvl {
                    if self.seen[u] { continue; }
                    if self.reason[u] != Reason::None && self.lit_redundant(u as u32, levels) { continue; }
                    break 'walk;
                } else {
                    break 'walk;
                }
            }
            open -= 1;
        }
        for &v in &marked { self.shrink_mark[v as usize] = false; }
        if uip.is_some() { self.stats.shrink_blocks += 1; }
        uip
    }

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
            // the next seen variable of the conflict level down the trail (a
            // lower-level literal can sit above it when trail order is not
            // level order)
            loop { idx -= 1; let t = self.trail[idx] as usize; if self.seen[t] && self.level[t] == current { break; } }
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
        if self.shrink && learnt.len() > 2 {
            // blocks from the highest level down: a block's reasons only reach
            // levels at or below it, so the lower blocks it consults are still
            // exactly as analysis left them
            self.min_clear.clear();
            for &q in &learnt[1..] { let v = q >> 1; self.seen[v as usize] = true; self.min_clear.push(v); }
            let levels = learnt[1..].iter().fold(0u32, |m, &q| m | 1 << (self.level[(q >> 1) as usize] & 31));
            let mut by_level: Vec<(u32, u32)> = learnt[1..].iter().map(|&q| (self.level[(q >> 1) as usize], q)).collect();
            by_level.sort_unstable_by(|a, b| b.0.cmp(&a.0));
            let mut out: Vec<u32> = vec![learnt[0]];
            let mut i = 0;
            while i < by_level.len() {
                let lvl = by_level[i].0;
                let mut k = i;
                while k < by_level.len() && by_level[k].0 == lvl { k += 1; }
                if k - i >= 2 {
                    let block: Vec<u32> = by_level[i..k].iter().map(|&(_, q)| q >> 1).collect();
                    match self.shrink_block(lvl, &block, levels) {
                        Some(u) => {
                            self.stats.shrunk_lits += (k - i - 1) as u64;
                            out.push(code(u, self.vals[u as usize] == Val::T));   // the UIP's false literal
                        }
                        None => out.extend(by_level[i..k].iter().map(|&(_, q)| q)),
                    }
                } else {
                    out.push(by_level[i].1);
                }
                i = k;
            }
            for k in 0..self.min_clear.len() { let x = self.min_clear[k]; self.seen[x as usize] = false; }
            learnt = out;
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
        if let Some(conflict) = self.propagate() {
            if self.proof.is_some() {
                let from_box = !matches!(conflict, Conflict::Clause(_));
                let mut lits = Vec::new();
                self.conflict_lits(conflict, &mut lits);
                self.proof_sync();
                if from_box { self.justify_box(&lits); }
                if let Some(p) = &mut self.proof { p.empty(); }
            }
            self.unsat_at_init = true;
            return false;
        }
        self.proof_sync();
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
        self.cancelled = self.cancel.as_ref().is_some_and(|c| c.load(std::sync::atomic::Ordering::Relaxed));
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
        for i in (0..self.elim.len()).rev() {
            let v = self.elim.var[i] as usize;
            let pos = code(v as u32, false);
            m[v] = self.elim.clauses(i).any(|j| { let c = self.elim.clause(j);
                c.contains(&pos) && !c.iter().any(|&l| (l >> 1) as usize != v && holds(m, l)) });
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
        // the reasons of the level-0 trail are cleared below, so any box
        // lemma among them has to reach the proof first
        self.proof_sync();
        let n = self.nvars;
        // the original clauses under the level-0 assignment
        // The working copy is a flat pool, not a Vec per clause: at 40 M
        // clauses the per-clause form was ~1.6 GB of container for
        // ~0.4 GB of literals (2026-09-21, doc/data/boxes_memory_2026-09-20.txt §6).
        struct Pool { lits: Vec<u32>, start: Vec<u32>, len: Vec<u32> }
        impl Pool {
            fn get(&self, i: usize) -> &[u32] {
                let s = self.start[i] as usize;
                &self.lits[s..s + self.len[i] as usize]
            }
            fn push(&mut self, c: &[u32]) {
                self.start.push(self.lits.len() as u32);
                self.len.push(c.len() as u32);
                self.lits.extend_from_slice(c);
            }
            fn n(&self) -> usize { self.start.len() }
        }
        // Reserved with room for the resolvents: capacity nobody writes is
        // free, while growing past an exact reservation copies the whole
        // pool at its fullest (a 1.6 GB transient on the 40 M-clause
        // instance, 2026-09-21).
        let mut cls = Pool { lits: Vec::with_capacity(2 * self.arena.len()),
                             start: Vec::with_capacity(2 * self.first_learnt), len: Vec::with_capacity(2 * self.first_learnt) };
        let mut buf: Vec<u32> = Vec::new();
        for ci in 0..self.first_learnt {
            if self.deleted[ci] || self.clause(ci).iter().any(|&l| self.lit_value(l) == Val::T) { continue; }
            buf.clear();
            buf.extend(self.clause(ci).iter().copied().filter(|&l| self.lit_value(l) != Val::F));
            debug_assert!(buf.len() >= 2, "level-0 propagation left a unit or empty clause");
            cls.push(&buf);
        }
        let learned: Vec<(Vec<u32>, u32, f64)> = (self.first_learnt..self.cstart.len())
            .filter(|&ci| !self.deleted[ci] && !self.clause(ci).iter().any(|&l| self.lit_value(l) == Val::T))
            .map(|ci| (self.clause(ci).iter().copied().filter(|&l| self.lit_value(l) != Val::F).collect(), self.learnt_lbd[ci - self.first_learnt], self.learnt_act[ci - self.first_learnt]))
            .collect();
        self.mem_mark("elim: working copy built");
        self.stats.clauses_before = cls.n() as u64;
        // Nothing below reads the store again until it is rebuilt from the
        // pool, so its buffers go now rather than sitting under the
        // occurrence lists and the resolvents: arena, index, watches and
        // binaries were ~3 GB of the 8.9 GB peak on the 40 M-clause
        // instance.  (The headers of the per-literal vectors stay; they
        // are the next item.)  Level-0 reasons that pointed into the store
        // are cleared where the store is rebuilt, as before -- no
        // propagation happens in between.
        self.arena = Vec::new(); self.cstart = Vec::new(); self.clen = Vec::new();
        self.watches.clear(); self.bins.clear();
        self.mem_mark("elim: old store freed");
        let mut alive = vec![true; cls.n()];
        // Occurrence lists with u32 indices, sized exactly by a counting
        // pass: half the entry size of usize, and no doubling slack.
        let mut cnt = vec![0u32; 2 * n];
        for i in 0..cls.n() { for &l in cls.get(i) { cnt[l as usize] += 1; } }
        let mut occ: Vec<Vec<u32>> = cnt.iter().map(|&k| Vec::with_capacity(k as usize)).collect();
        drop(cnt);
        for i in 0..cls.n() { for &l in cls.get(i) { occ[l as usize].push(i as u32); } }
        self.mem_mark("elim: occurrence lists built");
        let frozen: Vec<bool> = (0..n).map(|v| self.occ.get(v).is_some_and(|o| !o.is_empty()) || self.vals[v] != Val::U).collect();
        let resolve = |a: &[u32], b: &[u32], v: usize| -> Option<Vec<u32>> {
            let mut r: Vec<u32> = a.iter().chain(b.iter()).copied().filter(|&l| (l >> 1) as usize != v).collect();
            r.sort_unstable(); r.dedup();
            if r.windows(2).any(|w| w[0] >> 1 == w[1] >> 1) { return None; }   // tautology
            Some(r)
        };
        for _pass in 0..2 {
            let mut order: Vec<usize> = (0..n).filter(|&v| !frozen[v] && !self.eliminated[v]).collect();
            order.retain(|&v| occ[2 * v].iter().any(|&i| alive[i as usize]) || occ[2 * v + 1].iter().any(|&i| alive[i as usize]));
            order.sort_by_key(|&v| occ[2 * v].len() * occ[2 * v + 1].len());
            for v in order {
                let pos: Vec<usize> = occ[2 * v].iter().map(|&i| i as usize).filter(|&i| alive[i]).collect();
                let neg: Vec<usize> = occ[2 * v + 1].iter().map(|&i| i as usize).filter(|&i| alive[i]).collect();
                if pos.len() > 16 || neg.len() > 16 { continue; }
                let mut resolvents: Vec<Vec<u32>> = Vec::new();
                let mut ok = true;
                'outer: for &i in &pos {
                    for &j in &neg {
                        if let Some(r) = resolve(cls.get(i), cls.get(j), v) {
                            if r.len() > 20 || resolvents.len() >= pos.len() + neg.len() { ok = false; break 'outer; }
                            resolvents.push(r);
                        }
                    }
                }
                if !ok { continue; }
                for &i in pos.iter().chain(neg.iter()) { alive[i] = false; self.elim.push_clause(cls.get(i)); }
                self.elim.push_var(v as u32);
                self.eliminated[v] = true;
                self.stats.eliminated += 1;
                for r in resolvents {
                    let idx = cls.n() as u32;
                    for &l in &r { occ[l as usize].push(idx); }
                    cls.push(&r); alive.push(true);
                }
            }
        }
        // The occurrence lists have done their work; the rebuild below
        // allocates a whole new store, and they need not sit under it.
        drop(occ);
        self.mem_mark(&format!("elim: passes done, occurrence lists dropped; pool {} of {} M literals, {} of {} M clauses",
                               cls.lits.len() / 1_000_000, cls.lits.capacity() / 1_000_000,
                               cls.n() / 1_000_000, cls.start.capacity() / 1_000_000));
        // rebuild the clause store: the surviving originals, then the
        // learned clauses free of eliminated variables
        // The store was freed above; size it exactly for the survivors so
        // the rebuild does not double its way back up.
        let (mut kept_n, mut kept_lits) = (0usize, 0usize);
        for i in 0..cls.n() { if alive[i] { kept_n += 1; kept_lits += cls.len[i] as usize; } }
        let (lit_cap, cl_cap) = (with_headroom(kept_lits, 1 << 20), with_headroom(kept_n, 1 << 17));
        self.arena.reserve_exact(lit_cap); self.cstart.reserve_exact(cl_cap); self.clen.reserve_exact(cl_cap);
        self.deleted.clear(); self.learnt_lbd.clear(); self.learnt_act.clear(); self.learnt_used.clear();
        // The counts are keyed by clause index and everything is about to
        // be renumbered.
        self.eff_clause_hits.clear();
        self.first_learnt = 0;
        self.watches.clear(); self.bins.clear();
        for v in 0..n { if self.vals[v] != Val::U { self.reason[v] = Reason::None; } }   // level-0 reasons pointed into the old store
        // First the clauses alone, then the pool goes, then the watch lists
        // -- the largest part of the new store -- are sized and filled from
        // the store itself.  Learned clauses come last, as before, so every
        // per-literal list is in the same order as a one-pass rebuild.
        let mut kept = 0u64;
        let mut lits: Vec<Lit> = Vec::new();
        for i in 0..cls.n() {
            if !alive[i] { continue; }
            kept += 1;
            lits.clear();
            lits.extend(cls.get(i).iter().map(|&l| Lit { var: l >> 1, neg: l & 1 == 1 }));
            self.add_clause_impl(&lits, false);
        }
        self.stats.clauses_after = kept;
        drop(cls); drop(alive);
        self.mem_mark("elim: clauses rebuilt, pool dropped");
        self.attach_watches(0, self.cstart.len());
        self.mem_mark("elim: watch lists attached");
        for (c, lbd, act) in learned {
            if c.iter().any(|&l| self.eliminated[(l >> 1) as usize]) { continue; }
            self.add_learned(c, lbd, act);
        }
        self.mem_mark("elim: store rebuilt");
        self.qhead = 0;
    }

    pub fn solve(&mut self) -> Verdict {
        if !self.init() { return Verdict::Unsat; }
        self.mem_report("after init (level-0 simplification done)");
        let v = self.solve_under(&[]);
        self.mem_report("at the end of the search");
        if self.count_visits {
            let s = &self.stats;
            eprintln!("c boxes: propagation work: {} binary visits; {} watch visits, {} blocked, {} clause visits, {} literal steps; for {} propagations, {} conflicts",
                      s.bin_visits, s.watch_visits, s.blocker_hits, s.clause_visits, s.lit_steps, s.propagations, s.conflicts);
        }
        v
    }

    /// Whether to restart after a conflict that learned a clause of LBD
    /// `lbd` with `trail_len` literals assigned when it happened;
    /// `conflicts_here` / `restarts` count since this search began.
    fn restart_due(&mut self, lbd: u32, trail_len: u32, conflicts_here: u64, restarts: u64) -> bool {
        match self.restart {
            RestartMode::Luby => conflicts_here >= 64 * Self::luby(restarts),
            RestartMode::Ema => {
                if self.stabilize && self.stats.conflicts >= self.stable_toggle_at {
                    self.stable = !self.stable;
                    self.stable_len *= 2;
                    self.stable_toggle_at = self.stats.conflicts + self.stable_len;
                }
                self.glue_fast.update(lbd as f64);
                self.glue_slow.update(lbd as f64);
                if self.stable { return conflicts_here >= 512 * Self::luby(restarts); }
                conflicts_here >= 2 && self.glue_fast.value > self.restart_margin * self.glue_slow.value
            }
            RestartMode::Glucose => {
                if self.stabilize && self.stats.conflicts >= self.stable_toggle_at {
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
        if matches!(self.restart, RestartMode::Glucose | RestartMode::Ema) && let Some(next) = self.heap_peek_unassigned() {
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
        let mut cands: Vec<usize> = (self.first_learnt..self.cstart.len()).filter(|&ci| !self.deleted[ci] && self.learnt_lbd[ci - self.first_learnt] <= 6 && self.clen[ci] > 2).collect();
        cands.sort_by_key(|&ci| (self.learnt_lbd[ci - self.first_learnt], self.clen[ci]));
        for ci in cands {
            if self.stats.propagations > budget_end { break; }
            let lits = self.clause(ci).to_vec();
            // under the level-0 assignment
            if lits.iter().any(|&l| self.lit_value(l) == Val::T) { self.delete_clause(ci); continue; }
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
            self.clen[ci] = 0;
            let lbd = self.learnt_lbd[ci - self.first_learnt];
            let act = self.learnt_act[ci - self.first_learnt];
            self.add_learned(kept, lbd, act);
            if self.unsat_at_init { break; }
        }
        self.phase = saved_phase;
    }

    /// Add a learned clause at level 0 (an inprocessing result): a unit is
    /// assigned, the empty clause makes the engine unsatisfiable.
    /// Debug check (`BOXES_DEBUG_WATCHES=1`): after propagation has reached a
    /// fixpoint, no clause may have a false watch while it is neither
    /// satisfied nor fully false — that is the state in which a later conflict
    /// on the clause goes unseen.  Returns a description of the first
    /// violation.
    fn debug_watch_violation(&self) -> Option<String> {
        for ci in 0..self.cstart.len() {
            let len = self.clen[ci] as usize;
            if self.deleted[ci] || len < 3 { continue; }
            let c = self.clause(ci);
            if c.iter().any(|&l| self.lvals[l as usize] == Val::T) { continue; }
            let w_false = self.lvals[c[0] as usize] == Val::F || self.lvals[c[1] as usize] == Val::F;
            let some_open = c.iter().any(|&l| self.lvals[l as usize] == Val::U);
            // a false watch next to an open literal, with the other watch not
            // the single open one (a unit clause waiting in the queue is fine)
            let open = c.iter().filter(|&&l| self.lvals[l as usize] == Val::U).count();
            let both_false = self.lvals[c[0] as usize] == Val::F && self.lvals[c[1] as usize] == Val::F;
            if w_false && some_open && (both_false || open >= 2) {
                let show: Vec<(i32, Val, u32)> = c.iter().map(|&l| (if l & 1 == 1 { -((l >> 1) as i32 + 1) } else { (l >> 1) as i32 + 1 }, self.lvals[l as usize], self.level[(l >> 1) as usize])).collect();
                return Some(format!("clause {ci} (learnt: {}, level {}): {show:?}", ci >= self.first_learnt, self.decision_level()));
            }
        }
        None
    }

    /// Backward subsumption and self-subsuming resolution over the whole
    /// clause store, at level 0.
    ///
    /// For each clause `C`, shortest first, the rarest of its literals names
    /// the candidates `D` that could contain it; a 64-bit signature rejects
    /// most of them without touching the arena.  `C ⊆ D` deletes `D`;
    /// `C \ {l} ⊆ D` with `¬l ∈ D` drops `¬l` from `D` (the resolvent of the
    /// two, so an ordinary RUP addition for the proof).  Clauses that are a
    /// reason for an assigned literal are left alone, and binaries are never
    /// deleted because the implication lists do not carry deletions.
    fn subsume_round(&mut self) {
        const LEN_CAP: usize = 64;
        let budget: u64 = env_usize("BOXES_SUBSUME_BUDGET", 20_000_000) as u64;
        let mut work: u64 = 0;
        self.stats.subsume_rounds += 1;
        let n = self.cstart.len();
        // two signatures: over literals, which subsumption needs (`C ⊆ D`),
        // and over variables, which is all strengthening may assume (`C`'s
        // clashing literal appears in `D` negated, so its literal bit is
        // absent there — filtering strengthening on the literal signature
        // rejects every candidate, which is how the first version of this
        // round came to strengthen almost nothing).
        let mut sig: Vec<u64> = vec![0; n];
        let mut vsig: Vec<u64> = vec![0; n];
        let mut occ: Vec<Vec<u32>> = vec![Vec::new(); 2 * self.nvars];
        let mut cands: Vec<u32> = Vec::new();
        for ci in 0..n {
            let len = self.clen[ci] as usize;
            if self.deleted[ci] || len < 2 || len > LEN_CAP { continue; }
            let st = self.cstart[ci] as usize;
            let mut sg = 0u64;
            let mut vg = 0u64;
            for k in 0..len {
                let l = self.arena[st + k];
                sg |= 1u64 << (l & 63);
                vg |= 1u64 << ((l >> 1) & 63);
                occ[l as usize].push(ci as u32);
            }
            sig[ci] = sg;
            vsig[ci] = vg;
            cands.push(ci as u32);
        }
        cands.sort_by_key(|&ci| self.clen[ci as usize]);
        let mut mark: Vec<u32> = vec![0; 2 * self.nvars];
        let mut stamp: u32 = 0;
        let mut strengthen: Vec<(u32, u32)> = Vec::new();
        // A clause carries a constraint of the input formula when it is an
        // original or stands in for one (LBD 0, set below).  Deleting such a
        // clause is only sound while whatever replaces it is itself
        // permanent, and the property has to travel: a promoted clause that
        // is later strengthened or subsumed hands the duty on, or the input
        // constraint is lost and the engine answers SAT on an unsatisfiable
        // formula (measured on c3540, 2026-09-16).
        let is_permanent = |e: &Engine, ci: usize| -> bool {
            ci < e.first_learnt || e.learnt_lbd[ci - e.first_learnt] == 0
        };
        // a clause propagating an assigned literal is its reason: untouchable
        let is_reason = |e: &Engine, ci: usize| -> bool {
            let l0 = e.arena[e.cstart[ci] as usize];
            e.vals[(l0 >> 1) as usize] != Val::U && e.reason[(l0 >> 1) as usize] == Reason::Clause(ci as u32)
        };
        for idx in 0..cands.len() {
            if work > budget { break; }
            let ci = cands[idx] as usize;
            if self.deleted[ci] { continue; }
            let len = self.clen[ci] as usize;
            let st = self.cstart[ci] as usize;
            let lits: Vec<u32> = self.arena[st..st + len].to_vec();
            // the rarest literal of `C` names the candidates.  Both of its
            // occurrence lists are needed: a clause `D` that `C` strengthens
            // holds the clashing literal negated, so when the pivot is the
            // one that clashes, `D` sits in the opposite list.
            let Some(&pivot) = lits.iter().min_by_key(|&&l| occ[l as usize].len() + occ[(l ^ 1) as usize].len()) else { continue };
            stamp += 1;
            for &l in &lits { mark[l as usize] = stamp; }
            let others = std::mem::take(&mut occ[pivot as usize]);
            let clashing = std::mem::take(&mut occ[(pivot ^ 1) as usize]);
            for &cj in others.iter().chain(clashing.iter()) {
                let cj = cj as usize;
                if cj == ci || self.deleted[cj] { continue; }
                let lj = self.clen[cj] as usize;
                if lj < len || vsig[ci] & !vsig[cj] != 0 { continue; }
                work += lj as u64;
                let sj = self.cstart[cj] as usize;
                let (mut hit, mut neg, mut negl) = (0usize, 0usize, 0u32);
                for k in 0..lj {
                    let l = self.arena[sj + k];
                    if mark[l as usize] == stamp { hit += 1; }
                    else if mark[(l ^ 1) as usize] == stamp { neg += 1; negl = l; }
                }
                if neg == 0 && hit == len && sig[ci] & !sig[cj] == 0 {
                    if lj > 2 && !is_reason(self, cj) {
                        // deleting a permanent clause is only sound while the
                        // clause that subsumes it survives, so its subsumer
                        // inherits permanence
                        if is_permanent(self, cj) && !is_permanent(self, ci) {
                            self.learnt_lbd[ci - self.first_learnt] = 0;
                        }
                        self.delete_clause(cj);
                        self.stats.subsumed += 1;
                    }
                } else if neg == 1 && hit + 1 == len && !is_reason(self, cj) {
                    strengthen.push((cj as u32, negl));
                }
            }
            occ[pivot as usize] = others;
            occ[(pivot ^ 1) as usize] = clashing;
        }
        // apply the strengthenings: add the resolvent, then drop the original
        for (cj, negl) in strengthen {
            let cj = cj as usize;
            if self.deleted[cj] || is_reason(self, cj) { continue; }
            let lj = self.clen[cj] as usize;
            let sj = self.cstart[cj] as usize;
            let c: Vec<u32> = self.arena[sj..sj + lj].iter().copied().filter(|&l| l != negl).collect();
            if c.len() == lj { continue; }
            // strengthening a permanent clause replaces it, so the
            // replacement inherits its permanence; a merely learned clause is
            // redundant either way and keeps an ordinary LBD
            let lbd = if is_permanent(self, cj) { 0 } else { self.lbd(&c) };
            let act = self.cla_inc;
            self.add_learned(c, lbd, act);
            self.delete_clause(cj);
            self.stats.strengthened += 1;
            self.stats.strengthened_lits += 1;
            if self.unsat_at_init { return; }
        }
    }

    fn add_learned(&mut self, mut c: Vec<u32>, lbd: u32, act: f64) {
        c.sort_unstable(); c.dedup();
        // At level 0 a clause is watched on its first two literals, and a
        // literal already false there is never made false again, so its watch
        // would never be visited: with both watches on such literals the
        // clause could be falsified without anyone noticing.  Level-0 truths
        // are permanent too.  So a satisfied clause is dropped and false
        // literals are removed (each removal is a resolution with a level-0
        // unit, so the clause stays RUP for the proof).  Found by the model
        // self-check: a clause strengthened by subsumption was born with a
        // dead watch, and the engine answered SAT on an unsatisfiable shuffle
        // of c5315 under chronological backtracking.
        if self.trail_lim.is_empty() {
            if c.iter().any(|&l| self.lvals[l as usize] == Val::T) { return; }
            c.retain(|&l| self.lvals[l as usize] != Val::F);
        }
        if self.proof.is_some() { if c.is_empty() { if let Some(p) = &mut self.proof { p.empty(); } } else { self.log_learned(&c); } }
        match c.len() {
            0 => self.unsat_at_init = true,
            1 => { let l = c[0]; if !self.assign(l >> 1, if l & 1 == 1 { Val::F } else { Val::T }, Reason::None) { self.unsat_at_init = true; } else if self.propagate().is_some() { self.unsat_at_init = true; } }
            _ => {
                let ci = self.cstart.len() as u32;
                if c.len() == 2 {
                    self.bins.push(c[0] as usize, (c[1], ci));
                    self.bins.push(c[1] as usize, (c[0], ci));
                } else {
                    self.watches.push(c[0] as usize, (ci, c[1]));
                    self.watches.push(c[1] as usize, (ci, c[0]));
                }
                self.push_clause(&c);
                self.deleted.push(false);
                self.learnt_lbd.push(lbd);
                self.learnt_act.push(act);
                self.learnt_used.push(MAX_USED);
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
                self.eff_sample(conflict);
                let trail_len = self.trail.len() as u32;
                let from_box = !matches!(conflict, Conflict::Clause(_));
                let mut lits = Vec::new();
                self.conflict_lits(conflict, &mut lits);
                if from_box && self.proof.is_some() { let c = lits.clone(); self.justify_box(&c); }
                // A conflict whose literals all lie below the current level
                // is a conflict at the highest of their levels: analysis
                // starts there (it cannot happen while `live` tracks the
                // trail, but a conflict with no current-level literal would
                // otherwise walk off the trail).
                let top = lits.iter().map(|&q| self.level[(q >> 1) as usize] as usize).max().unwrap_or(0);
                if top < self.decision_level() { self.backjump(top.max(base)); }
                if self.decision_level() <= base {
                    if base == 0 { self.proof_sync(); if let Some(p) = &mut self.proof { p.empty(); } }
                    return Verdict::Unsat;
                }
                if self.stats.conflicts & 255 == 0 && let Some(c) = &self.cancel && c.load(std::sync::atomic::Ordering::Relaxed) { return Verdict::Unknown; }
                let (learnt, bj) = self.analyze(lits);
                self.log_learned(&learnt);
                let now = self.decision_level();
                // CaDiCaL's determine_actual_backtrack_level
                let target = if !self.chrono || learnt.len() == 1 || !assumptions.is_empty() || bj + 1 >= now {
                    bj
                } else if now - bj > self.chrono_levels {
                    self.stats.chrono_backtracks += 1;
                    now - 1
                } else if self.chrono_reuse {
                    // the most active variable assigned above the asserting level
                    let start = self.trail_lim[bj];
                    let (mut best_pos, mut best_act) = (start, f64::NEG_INFINITY);
                    for i in start..self.trail.len() {
                        let a = self.activity[self.trail[i] as usize];
                        if a > best_act { best_act = a; best_pos = i; }
                    }
                    // keep every level whose decision sits at or before it
                    let mut res = bj;
                    while res < now - 1 && self.trail_lim[res] <= best_pos { res += 1; }
                    if res > bj { self.stats.chrono_backtracks += 1; }
                    res
                } else { bj };
                self.backjump(target.max(base));
                let l0 = learnt[0];
                let mut lbd = 1;
                if learnt.len() == 1 {
                    self.assign(l0 >> 1, if l0 & 1 == 1 { Val::F } else { Val::T }, Reason::None);
                } else {
                    let ci = self.cstart.len() as u32;
                    if learnt.len() == 2 {
                        self.bins.push(learnt[0] as usize, (learnt[1], ci));
                        self.bins.push(learnt[1] as usize, (learnt[0], ci));
                    } else {
                        self.watches.push(learnt[0] as usize, (ci, learnt[1]));
                        self.watches.push(learnt[1] as usize, (ci, learnt[0]));
                    }
                    lbd = self.lbd(&learnt);
                    self.push_clause(&learnt);
                    self.deleted.push(false);
                    self.learnt_lbd.push(lbd);
                    self.learnt_act.push(self.cla_inc);
                    self.learnt_used.push(MAX_USED);
                    self.assign(l0 >> 1, if l0 & 1 == 1 { Val::F } else { Val::T }, Reason::Clause(ci));
                }
                self.var_inc *= 1.0 / 0.95;
                self.cla_inc *= 1.0 / 0.999;
                if self.reduce_at == 0 { self.reduce_at = self.stats.conflicts + self.reduce_start as u64; }
                if self.stats.conflicts >= self.reduce_at {
                    self.reduce_db();
                    self.reduce_start += self.reduce_step;
                    self.reduce_at = self.stats.conflicts + self.reduce_start as u64;
                }
                if self.restart_due(lbd, trail_len, conflicts_here, restarts) {
                    restarts += 1; conflicts_here = 0;
                    self.restart(base);
                    if self.subsume && base == 0 && self.stats.conflicts >= self.subsume_at {
                        self.subsume_at = self.stats.conflicts + self.subsume_interval;
                        self.subsume_interval += self.subsume_interval / 2;
                        self.backjump(0);
                        self.subsume_round();
                        if self.unsat_at_init { return Verdict::Unsat; }
                        if std::env::var("BOXES_DEBUG_WATCHES").is_ok() && self.propagate().is_none() {
                            if let Some(v) = self.debug_watch_violation() { panic!("watch invariant broken after a subsumption round: {v}"); }
                        }
                    }
                    if self.inprocess && !self.chrono && base == 0 && self.stats.conflicts >= self.inprocess_at {
                        self.inprocess_at = self.stats.conflicts + self.inprocess_interval;
                        self.inprocess_interval += 10_000;
                        self.backjump(0);
                        self.inprocess_round();
                        if self.unsat_at_init { return Verdict::Unsat; }
                    }
                }
                continue;
            }
            if self.cancelled { return Verdict::Unknown; }
            if let Some(max) = self.max_decisions && self.stats.decisions >= max { return Verdict::Unknown; }
            if self.debug_watches && self.stats.decisions % 64 == 0 {
                if let Some(v) = self.debug_watch_violation() { panic!("watch invariant broken at a decision (conflicts {}): {v}", self.stats.conflicts); }
            }
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
    use crate::cadical;

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
    /// The rule itself, on hand-made cases.
    #[test]
    fn subsume_round_does_what_it_says() {
        // (1 2) subsumes (1 2 3); (1 2) and (-1 2 3) resolve to (2 3)
        let mut e = Engine::from_cnf(4, &[vec![1, 2], vec![1, 2, 3], vec![-1, 2, 3, 4]]);
        assert!(e.init());
        e.subsume_round();
        eprintln!("subsumed {} strengthened {} (clauses {})", e.stats.subsumed, e.stats.strengthened, e.nclauses());
        for ci in 0..e.nclauses() { if !e.deleted[ci] { eprintln!("  kept {:?}", e.clause(ci).iter().map(|&l| if l & 1 == 1 { -((l >> 1) as i32 + 1) } else { (l >> 1) as i32 + 1 }).collect::<Vec<_>>()); } }
        assert_eq!(e.stats.subsumed, 1, "(1 2) should subsume (1 2 3)");
        assert_eq!(e.stats.strengthened, 1, "(1 2) should strengthen (-1 2 3 4) to (2 3 4)");
    }

    /// Subsumption runs after variable elimination on the real instances,
    /// so the two have to be tested together: BVE's resolvents subsume the
    /// originals they came from, and a wrong deletion there loses a clause
    /// the reconstructed model must still satisfy.
    #[test]
    fn subsumption_with_elimination_vs_bruteforce() {
        let mut seed: u64 = 0xB0_5E_1234_9ABC;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut subsumed_total = 0u64;
        for trial in 0..400 {
            // dense enough that elimination cannot dissolve the instance and
            // the search has real work left for subsumption to help with
            let n = 10 + (rnd() % 8) as usize;
            let m = 4 * n + (rnd() % (3 * n as u64)) as usize;
            let mut cls: Vec<Vec<i32>> = Vec::new();
            for _ in 0..m {
                let len = 2 + (rnd() % 2) as usize;
                let mut c = Vec::new();
                for _ in 0..len { let v = (rnd() % n as u64) as i32 + 1; c.push(if rnd() % 2 == 0 { v } else { -v }); }
                // half the time also plant something for subsumption to find:
                // a superset of `c` (subsumable) or `c` with one literal
                // flipped (strengthenable)
                match rnd() % 4 {
                    0 => { let mut d = c.clone(); for _ in 0..1 + rnd() % 2 { let v = (rnd() % n as u64) as i32 + 1; d.push(if rnd() % 2 == 0 { v } else { -v }); } cls.push(d); }
                    1 => { let mut d = c.clone(); if !d.is_empty() { d[0] = -d[0]; } let v = (rnd() % n as u64) as i32 + 1; d.push(if rnd() % 2 == 0 { v } else { -v }); cls.push(d); }
                    _ => {}
                }
                cls.push(c);
            }
            let brute = (0..1u32 << n).any(|bits| check_model(&cls, &(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let mut e = Engine::from_cnf(n, &cls);
            e.subsume = true; e.subsume_at = 0; e.subsume_interval = 1;
            e.reduce_start = 30;   // the reduction must run: subsumption deletes
                                   // originals, and their survivor must outlive it
            let ok = e.simplify();
            let v = if ok {
                let inited = e.init();
                if inited { e.subsume_round(); }
                if e.unsat_at_init { Verdict::Unsat } else { e.solve_under(&[]) }
            } else { Verdict::Unsat };
            subsumed_total += e.stats.subsumed + e.stats.strengthened;
            match v {
                Verdict::Sat(model) => {
                    assert!(brute, "trial {trial}: engine SAT, brute UNSAT: {cls:?}");
                    assert!(check_model(&cls, &model), "trial {trial}: model violates the original: {cls:?}");
                }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT: {cls:?}"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
        assert!(subsumed_total > 0, "subsumption never fired");
    }

    /// Chronological backtracking changes the trail invariants everything else
    /// leans on (level order, the watch discipline, the analysis walk), so it
    /// is tested with backtracking forced chronological on every conflict
    /// (`chrono_levels = 0`), against brute force on tables and clauses.
    #[test]
    fn chrono_vs_bruteforce() {
        let mut seed: u64 = 0xC4_0E0_BAC4_7EAC;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut chrono_total = 0u64; let mut kept_total = 0u64;
        for trial in 0..500 {
            let n = 8 + (rnd() % 7) as usize;
            let m = 3 * n + (rnd() % (2 * n as u64)) as usize;
            let cls: Vec<Vec<i32>> = (0..m).map(|_| {
                let mut c: Vec<i32> = Vec::new();
                while c.len() < 3 { let v = (rnd() % n as u64) as i32 + 1; if !c.iter().any(|&x| x.abs() == v) { c.push(if rnd() % 2 == 0 { v } else { -v }); } }
                c
            }).collect();
            // sometimes tables too, whose propagations keep the current level
            let mut boxes: Vec<Vec<Vec<Lit>>> = Vec::new();
            for _ in 0..(rnd() % 3) as usize {
                let k = 2 + (rnd() % 3) as usize;
                let mut cols: Vec<u32> = Vec::new();
                while cols.len() < k.min(n) { let v = (rnd() % n as u64) as u32; if !cols.contains(&v) { cols.push(v); } }
                let mut rows: Vec<Vec<Lit>> = Vec::new();
                for _ in 0..2 + (rnd() % 5) as usize {
                    let mut row = Vec::new();
                    for &v in &cols { if rnd() % 3 != 0 { let neg = rnd() % 2 == 0; row.push(Lit { var: v, neg }); } }
                    rows.push(row);
                }
                boxes.push(rows);
            }
            let row_holds = |row: &[Lit], mm: &[bool]| row.iter().all(|l| mm[l.var as usize] == !l.neg);
            let holds = |mm: &[bool]| boxes.iter().all(|rows| rows.iter().any(|r| row_holds(r, mm))) && check_model(&cls, mm);
            let brute = (0..1u32 << n).any(|bits| holds(&(0..n).map(|i| bits >> i & 1 == 1).collect::<Vec<_>>()));
            let mut e = Engine::new(n, boxes.iter().map(|rows| TableBox::new(rows.clone())).collect());
            for c in &cls { e.add_clause(&c.iter().map(|&l| lit_of_dimacs(l)).collect::<Vec<_>>()); }
            e.chrono = true; e.chrono_levels = 0;
            e.reduce_start = 20; e.subsume_at = 5; e.subsume_interval = 5;
            e.restart = if trial % 2 == 0 { RestartMode::Luby } else { RestartMode::Glucose };
            match e.solve() {
                Verdict::Sat(mm) => { assert!(brute, "trial {trial}: engine SAT, brute UNSAT"); assert!(holds(&mm), "trial {trial}: model violates the formula: {cls:?} {boxes:?}"); }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT: {cls:?} {boxes:?}"),
                Verdict::Unknown => panic!("no budget set"),
            }
            chrono_total += e.stats.chrono_backtracks; kept_total += e.stats.chrono_kept;
        }
        eprintln!("chronological backtracks {chrono_total}, literals kept out of order {kept_total}");
        assert!(chrono_total > 0 && kept_total > 0, "chronological backtracking never kept a literal: the test exercises nothing");
    }

    /// Pigeonhole with every search feature on and backtracking forced
    /// chronological: unsatisfiable, so any model is a soundness failure.
    /// This is the shape that exposed kept literals going unpropagated.
    #[test]
    fn chrono_on_pigeonhole() {
        for p in 5..=9 {
            let (n, cls) = php(p, p - 1);
            for simplify in [false, true] {
                let mut e = Engine::from_cnf(n, &cls);
                e.chrono = true; e.chrono_levels = 0; e.shrink = true;
                e.reduce_start = 100; e.subsume_at = 50; e.subsume_interval = 50;
                let ok = if simplify { e.simplify() } else { true };
                let v = if ok { e.solve() } else { Verdict::Unsat };
                if let Verdict::Sat(m) = &v { panic!("PHP-{p}-{} (simplify {simplify}): SAT, model valid: {}", p - 1, check_model(&cls, m)); }
                assert_eq!(v, Verdict::Unsat, "PHP-{p}-{}", p - 1);
            }
        }
    }

    /// The watch invariant, checked during search while subsumption runs
    /// often, with and without chronological backtracking.  A clause added at
    /// level 0 with a watch on a literal already false there has a watch that
    /// is never visited again; subsumption's strengthening used to create
    /// exactly that, and the engine then answered SAT on an unsatisfiable
    /// formula.  `debug_watches` panics on the first such clause.
    #[test]
    fn watch_invariant_holds_under_subsumption() {
        let mut seed: u64 = 0x0D0D_EAD0_5A7C_4411;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut strengthened = 0u64;
        for trial in 0..40 {
            let n = 120 + (rnd() % 80) as usize;
            let m = (4.2 * n as f64) as usize;
            let cls: Vec<Vec<i32>> = (0..m).map(|_| {
                let mut c: Vec<i32> = Vec::new();
                while c.len() < 3 { let v = (rnd() % n as u64) as i32 + 1; if !c.iter().any(|&x| x.abs() == v) { c.push(if rnd() % 2 == 0 { v } else { -v }); } }
                c
            }).collect();
            let mut cad: cadical::Solver<cadical::Timeout> = cadical::Solver::new();
            for c in &cls { cad.add_clause(c.iter().copied()); }
            let expect = cad.solve().expect("cadical");
            let mut e = Engine::from_cnf(n, &cls);
            e.debug_watches = true;
            e.chrono = trial % 2 == 1; e.chrono_levels = (trial % 4) as usize;
            e.shrink = trial % 3 != 0;
            e.reduce_start = 60; e.subsume_at = 10; e.subsume_interval = 10;
            let v = e.solve();
            strengthened += e.stats.strengthened;
            match v {
                Verdict::Sat(mm) => { assert!(expect, "trial {trial}: engine SAT, CaDiCaL UNSAT"); assert!(check_model(&cls, &mm), "trial {trial}: bad model"); }
                Verdict::Unsat => assert!(!expect, "trial {trial}: engine UNSAT, CaDiCaL SAT"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
        assert!(strengthened > 0, "no clause was strengthened: the test exercises nothing");
    }

    /// The same at a size where out-of-order trails get long, against CaDiCaL.
    #[test]
    fn chrono_vs_cadical() {
        let mut seed: u64 = 0x0B0B_C4C4_1234_5555;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let mut kept_total = 0u64;
        for trial in 0..60 {
            let n = 90 + (rnd() % 60) as usize;
            let m = (4.2 * n as f64) as usize + (rnd() % 12) as usize;
            let cls: Vec<Vec<i32>> = (0..m).map(|_| {
                let mut c: Vec<i32> = Vec::new();
                while c.len() < 3 { let v = (rnd() % n as u64) as i32 + 1; if !c.iter().any(|&x| x.abs() == v) { c.push(if rnd() % 2 == 0 { v } else { -v }); } }
                c
            }).collect();
            let mut cad: cadical::Solver<cadical::Timeout> = cadical::Solver::new();
            for c in &cls { cad.add_clause(c.iter().copied()); }
            let expect = cad.solve().expect("cadical");
            let mut e = Engine::from_cnf(n, &cls);
            e.chrono = true; e.chrono_levels = (trial % 3) as usize;   // 0, 1, 2: always, and nearly always, chronological
            e.shrink = trial % 2 == 0;
            e.reduce_start = 200; e.subsume_at = 50; e.subsume_interval = 50;
            e.restart = if trial % 2 == 0 { RestartMode::Luby } else { RestartMode::Glucose };
            let ok = e.simplify();
            let v = if ok { e.solve() } else { Verdict::Unsat };
            kept_total += e.stats.chrono_kept;
            match v {
                Verdict::Sat(mm) => { assert!(expect, "trial {trial}: engine SAT, CaDiCaL UNSAT"); assert!(check_model(&cls, &mm), "trial {trial}: model violates the formula"); }
                Verdict::Unsat => assert!(!expect, "trial {trial}: engine UNSAT, CaDiCaL SAT"),
                Verdict::Unknown => panic!("no budget set"),
            }
        }
        eprintln!("literals kept out of order: {kept_total}");
        assert!(kept_total > 0, "no literal was ever kept out of order");
    }

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
            e.chrono = false;   // vivification assumes a level-ordered trail and is off under chrono
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
            eprintln!("trial {trial}: {} conflicts, {} learned, {ndel} deleted", e.stats.conflicts, e.nclauses() - e.first_learnt);
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
        eprintln!("php(7,6): {} conflicts, {} learned, {ndel} deleted", e.stats.conflicts, e.nclauses() - e.first_learnt);
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
    // ── certified refutations (§4 of the design doc; `proof.rs`) ──────

    /// Replay a DRAT proof: every step must be RUP over the clauses before
    /// it, and the last must be the empty clause.  A second, deliberately
    /// naive implementation of the rule the prover has to satisfy — the
    /// external gate is `drat-trim` on the generated files.
    fn rup_replay(nvars: usize, formula: &[Vec<i32>], steps: &[Vec<i32>]) -> Result<(), String> {
        let mut cls: Vec<Vec<i32>> = formula.to_vec();
        for (k, step) in steps.iter().enumerate() {
            let mut val: Vec<Option<bool>> = vec![None; nvars + 1];
            let mut tautology = false;
            for &l in step {
                let v = l.unsigned_abs() as usize;
                let want = l < 0;                       // ¬step: the literal is false
                match val[v] { Some(b) if b != want => tautology = true, _ => val[v] = Some(want) }
            }
            if !tautology {
                let mut conflict = false;
                let mut changed = true;
                while changed && !conflict {
                    changed = false;
                    for c in &cls {
                        let mut open: Option<i32> = None;
                        let mut count = 0;
                        let mut sat = false;
                        for &l in c {
                            match val[l.unsigned_abs() as usize] {
                                Some(b) if b == (l > 0) => { sat = true; break; }
                                Some(_) => {}
                                None => { open = Some(l); count += 1; }
                            }
                        }
                        if sat { continue; }
                        match (count, open) {
                            (0, _) => { conflict = true; break; }
                            (1, Some(l)) => { val[l.unsigned_abs() as usize] = Some(l > 0); changed = true; }
                            _ => {}
                        }
                    }
                }
                if !conflict { return Err(format!("step {k} is not RUP: {step:?}")); }
            }
            cls.push(step.clone());
        }
        match steps.last() {
            Some(s) if s.is_empty() => Ok(()),
            _ => Err("the proof does not end in the empty clause".into()),
        }
    }

    /// A `k`-bit ripple-carry adder `a + b = s` (carry-in 0) in two forms:
    /// the Tseitin gate clauses (the box source) and one full-adder table
    /// per bit.  Variables: a_i, b_i, c_i, s_i, then three internals per
    /// cell.  Returns (nvars, gate clauses, boxes).
    fn adder_chain(k: usize) -> (usize, Vec<Vec<i32>>, Vec<TableBox>) {
        let (a, b, c, s) = (|i: usize| i as i32 + 1, |i: usize| (k + i) as i32 + 1,
                            |i: usize| (2 * k + i) as i32 + 1, |i: usize| (3 * k + i) as i32 + 2);
        let base = 4 * k as i32 + 1;
        let (u, v, w) = (|i: usize| base + 3 * i as i32 + 1, |i: usize| base + 3 * i as i32 + 2, |i: usize| base + 3 * i as i32 + 3);
        let and = |z: i32, x: i32, y: i32| vec![vec![-z, x], vec![-z, y], vec![z, -x, -y]];
        let or  = |z: i32, x: i32, y: i32| vec![vec![z, -x], vec![z, -y], vec![-z, x, y]];
        let xor = |z: i32, x: i32, y: i32| vec![vec![-z, x, y], vec![-z, -x, -y], vec![z, -x, y], vec![z, x, -y]];
        let mut gates = Vec::new();
        let mut boxes = Vec::new();
        for i in 0..k {
            gates.extend(and(u(i), a(i), b(i)));
            gates.extend(and(v(i), w(i), c(i)));
            gates.extend(or(c(i + 1), u(i), v(i)));
            gates.extend(xor(w(i), a(i), b(i)));
            gates.extend(xor(s(i), w(i), c(i)));
            // the cell's table over (a_i, b_i, c_i, s_i, c_i+1), model polarity
            let cols = [a(i), b(i), c(i), s(i), c(i + 1)];
            let rows: Vec<Vec<Lit>> = (0..8).map(|m: u32| {
                let (x, y, ci) = (m & 1, (m >> 1) & 1, (m >> 2) & 1);
                let sum = x ^ y ^ ci;
                let co = ((x + y + ci) >= 2) as u32;
                [x, y, ci, sum, co].iter().enumerate()
                    .map(|(j, &bit)| Lit { var: cols[j] as u32 - 1, neg: bit == 0 }).collect()
            }).collect();
            boxes.push(TableBox::new(rows));
        }
        (base as usize + 3 * k, gates, boxes)
    }

    /// `live_count` is a cache of a popcount, and a cache that drifts from
    /// what it caches is worse than no cache: the dead-box test reads it
    /// instead of scanning the words, so a stale count either invents a
    /// conflict or hides one.  The `debug_assert` in `propagate` checks it
    /// on every dequeue of every debug run; this pins the two paths that
    /// the assert alone would not distinguish — the incremental subtraction
    /// in `apply_kills`, and the wholesale restore in `backjump`.
    fn counts_agree(e: &Engine) {
        for b in 0..e.hdr.len() {
            let h = e.hdr[b];
            let (off, nw) = (h.off as usize, h.nw as usize);
            let want: u32 = (0..nw).map(|w| e.live[off + w].count_ones()).sum();
            assert_eq!(e.live_count[b], want, "box {b}: count {} but {want} rows live", e.live_count[b]);
        }
    }

    /// The boxed form of the adder — tables and the units, no gate clauses.
    /// With the gates present every conflict arrives through unit
    /// propagation and the tables never fail at all.
    fn boxed_adder(k: usize, maxbits: usize, sum: u64) -> Engine {
        let (n, _gates, boxes) = adder_chain(k);
        let mut e = Engine::new(n, boxes);
        for c in &adder_units(k, maxbits, sum) {
            e.add_clause(&c.iter().map(|&l| lit_of_dimacs(l)).collect::<Vec<_>>());
        }
        e
    }

    /// Pigeonhole as tables only: one exactly-one box per pigeon (one row
    /// per hole) and one at-most-one box per hole (all-empty, plus one row
    /// per pigeon).  Unlike the adder, GAC over these cannot refute it —
    /// the pigeonhole is the standard example of a formula whose
    /// unsatisfiability no amount of local consistency sees — so the engine
    /// has to search, and the tables are where it fails.  That is what a
    /// study of box constrainedness needs.
    fn boxed_php(pigeons: usize, holes: usize) -> Engine {
        let x = |p: usize, h: usize| (p * holes + h) as u32;
        let mut boxes = Vec::new();
        for p in 0..pigeons {
            boxes.push(TableBox::new((0..holes).map(|j|
                (0..holes).map(|h| Lit { var: x(p, h), neg: h != j }).collect()
            ).collect()));
        }
        for h in 0..holes {
            let mut rows: Vec<Vec<Lit>> = vec![(0..pigeons).map(|p| Lit { var: x(p, h), neg: true }).collect()];
            rows.extend((0..pigeons).map(|i|
                (0..pigeons).map(|p| Lit { var: x(p, h), neg: p != i }).collect::<Vec<_>>()
            ));
            boxes.push(TableBox::new(rows));
        }
        Engine::new(pigeons * holes, boxes)
    }

    #[test]
    fn live_counts_track_the_masks() {
        // UNSAT with real search, so the counts go through the incremental
        // subtraction and the wholesale restore many times over.
        let mut e = boxed_php(8, 7);
        e.set_eff_study(true);   // what drives the maintenance being checked
        assert_eq!(e.solve(), Verdict::Unsat);
        counts_agree(&e);
        assert!(e.stats.eff.box_conflicts > 0, "the fixture should fail inside the tables");

        // Propagation only: the boxed adder refutes with no conflict at all
        // (GAC over the cells is enough), which exercises `apply_kills`
        // without ever restoring a snapshot.
        let mut e = boxed_adder(8, 4, 200);
        e.set_eff_study(true);
        assert_eq!(e.solve(), Verdict::Unsat);
        counts_agree(&e);
        assert_eq!(e.stats.conflicts, 0, "the boxed adder should not need to search");

        // SAT, so the run ends mid-trail with counts reflecting a partial
        // assignment rather than a refutation.
        let mut e = boxed_adder(8, 8, 200);
        e.set_eff_study(true);
        assert!(matches!(e.solve(), Verdict::Sat(_)));
        counts_agree(&e);
    }

    #[test]
    fn the_eff_study_ranks_the_conflicting_box() {
        let mut e = boxed_php(8, 7);
        e.set_eff_study(true);
        assert_eq!(e.solve(), Verdict::Unsat);
        let s = &e.stats.eff;
        assert!(s.sampled > 0, "no box conflict was ranked: {s:?}");
        assert_eq!(s.sampled + s.unsampled, s.box_conflicts, "every box conflict is sampled or explained");
        assert_eq!(s.deciles.iter().sum::<u64>(), s.sampled, "every sample lands in exactly one decile");
        assert!(s.top1 <= s.top10 && s.top10 <= s.sampled);
        assert!(s.conflict_rows > 0 && s.population_rows > 0.0);
        // The ranking is over boxes, so a conflict in a clause is not one.
        assert!(s.clause_conflicts + s.box_conflicts >= e.stats.conflicts);
        // This fixture is boxes only: every clause it can fail on was
        // learned during the search, so none of them is structure a
        // translator could ever have absorbed.
        assert_eq!(s.clause_conflicts, s.clause_conflicts_learned);
        let (t1, t10, hit, all) = e.eff_concentration().expect("the study counts per-box failures");
        assert_eq!(all, 15, "8 pigeon boxes and 7 hole boxes");
        assert!(hit > 0 && hit <= all);
        assert!(t1 <= t10 && t10 <= 1.0 && t10 > 0.0);
    }

    /// The two conflict tallies are free and always on — they bound what a
    /// box-guided heuristic could steer at all — while the ranking that
    /// costs O(boxes) per conflict waits to be asked for.
    /// The grace period decides which learned clauses survive a reduction,
    /// so it changes the search on every instance that reduces at all — and
    /// must change no answer.  Deleting a clause that is still a reason, or
    /// sparing nothing and collapsing the database, would both show up here
    /// as a disagreement with brute force.
    #[test]
    fn used_grace_vs_bruteforce() {
        let mut seed: u64 = 0x51ED_0A27_1CE5_11FE;
        let mut rnd = || { seed ^= seed << 13; seed ^= seed >> 7; seed ^= seed << 17; seed };
        let (mut spared, mut promoted) = (0u64, 0u64);
        for trial in 0..400 {
            let n = 8 + (rnd() % 7) as usize;
            let m = 4 * n + (rnd() % (3 * n as u64)) as usize;
            let cls: Vec<Vec<i32>> = (0..m).map(|_| {
                let mut c: Vec<i32> = Vec::new();
                while c.len() < 3 {
                    let v = (rnd() % n as u64) as i32 + 1;
                    if !c.iter().any(|&x| x.abs() == v) { c.push(if rnd() % 2 == 0 { v } else { -v }); }
                }
                c
            }).collect();
            let brute = (0..1u32 << n).any(|bits| {
                let m: Vec<bool> = (0..n).map(|i| bits >> i & 1 == 1).collect();
                check_model(&cls, &m)
            });
            let mut e = Engine::from_cnf(n, &cls);
            e.used_grace = true;
            e.promote = true;
            // Reduce constantly, so a short random instance still exercises
            // the sparing and the decay many times over.
            e.reduce_start = 8;
            e.reduce_step = 8;
            match e.solve() {
                Verdict::Sat(m) => {
                    assert!(brute, "trial {trial}: engine SAT, brute UNSAT");
                    assert!(check_model(&cls, &m), "trial {trial}: bad model");
                }
                Verdict::Unsat => assert!(!brute, "trial {trial}: engine UNSAT, brute SAT"),
                Verdict::Unknown => panic!("no budget set"),
            }
            spared += e.stats.spared;
            promoted += e.stats.promoted;
        }
        assert!(spared > 0, "the grace period never spared a clause");
        assert!(promoted > 0, "no clause ever had its glue improve");
    }

    /// With the knobs off nothing changes: same verdicts, and the counters
    /// stay at zero, so the default path is the one that has been measured
    /// all along.
    #[test]
    fn the_grace_period_is_off_by_default() {
        let mut e = boxed_php(9, 8);
        assert!(!e.used_grace && !e.promote, "BOXES_USED/BOXES_PROMOTE must default off");
        assert_eq!(e.solve(), Verdict::Unsat);
        assert_eq!((e.stats.spared, e.stats.promoted), (0, 0));
        assert!(e.stats.reductions > 0, "the fixture should reduce at least once ({} conflicts)", e.stats.conflicts);
    }

    #[test]
    fn the_study_is_off_unless_asked_for() {
        let mut e = boxed_php(7, 6);
        assert!(!e.eff_study, "BOXES_EFF_STUDY must not be on by default");
        assert_eq!(e.solve(), Verdict::Unsat);
        let s = &e.stats.eff;
        assert!(s.box_conflicts > 0, "{s:?}");
        assert_eq!((s.sampled, s.unsampled, s.top1, s.conflict_rows), (0, 0, 0, 0));
        assert_eq!(s.deciles, [0; 10]);
    }

    /// Units fixing a and b free below `maxbits`, carry-in 0 and the sum to
    /// `sum` — unsatisfiable when `sum` exceeds what those bits can reach.
    fn adder_units(k: usize, maxbits: usize, sum: u64) -> Vec<Vec<i32>> {
        let (a, b, c, s) = (|i: usize| i as i32 + 1, |i: usize| (k + i) as i32 + 1,
                            |i: usize| (2 * k + i) as i32 + 1, |i: usize| (3 * k + i) as i32 + 2);
        let mut units = vec![vec![-c(0)]];
        for i in maxbits..k { units.push(vec![-a(i)]); units.push(vec![-b(i)]); }
        for i in 0..k { units.push(if sum >> i & 1 == 1 { vec![s(i)] } else { vec![-s(i)] }); }
        units.push(if sum >> k & 1 == 1 { vec![c(k)] } else { vec![-c(k)] });
        units
    }

    #[test]
    fn drat_proof_of_a_clausal_refutation_replays() {
        let (nvars, cls) = php(5, 4);
        let mut e = Engine::from_cnf(nvars, &cls);
        e.set_proof(proof::Proof::buffer());
        assert_eq!(e.solve(), Verdict::Unsat);
        let p = e.proof.as_mut().expect("proof");
        assert!(p.incomplete.is_none(), "{:?}", p.incomplete);
        let steps = p.take_buffer();
        assert!(steps.len() > 1, "a pigeonhole refutation takes more than one step");
        rup_replay(nvars, &cls, &steps).unwrap();
    }

    /// Shrinking and chronological backtracking both change which clauses the
    /// search learns and in what order; neither may produce a step that is not
    /// RUP.  PHP-7-6 with every search feature on, replayed naively.
    #[test]
    fn drat_proof_with_every_search_feature_replays() {
        let (nvars, cls) = php(7, 6);
        for (shrink, chrono) in [(true, false), (false, true), (true, true)] {
            let mut e = Engine::from_cnf(nvars, &cls);
            e.shrink = shrink; e.chrono = chrono; e.chrono_levels = 0;
            e.reduce_start = 100; e.subsume_at = 40; e.subsume_interval = 40;
            e.set_proof(proof::Proof::buffer());
            assert_eq!(e.solve(), Verdict::Unsat);
            let p = e.proof.as_mut().expect("proof");
            assert!(p.incomplete.is_none(), "{:?}", p.incomplete);
            let steps = p.take_buffer();
            rup_replay(nvars, &cls, &steps).unwrap_or_else(|err| panic!("shrink {shrink} chrono {chrono}: {err}"));
        }
    }

    /// The box lemmas are the point: a table propagates to generalized arc
    /// consistency, which unit propagation over the gate clauses does not
    /// reach, so each one is derived before the clause that used it.
    #[test]
    fn drat_proof_of_a_boxed_refutation_replays() {
        let k = 8;
        let (nvars, gates, boxes) = adder_chain(k);
        let units = adder_units(k, 4, 200);   // a, b < 16 cannot sum to 200
        let mut e = Engine::new(nvars, boxes);
        for c in &units { e.add_clause(&c.iter().map(|&l| lit_of_dimacs(l)).collect::<Vec<_>>()); }
        e.set_proof(proof::Proof::buffer());
        e.set_box_source(&gates);
        assert_eq!(e.solve(), Verdict::Unsat);
        let p = e.proof.as_mut().expect("proof");
        assert!(p.incomplete.is_none(), "{:?}", p.incomplete);
        assert!(p.lemmas > 0, "the refutation used no box lemma");
        let steps = p.take_buffer();
        // the proof certifies the ORIGINAL formula: gate clauses plus units
        let formula: Vec<Vec<i32>> = gates.iter().chain(units.iter()).cloned().collect();
        rup_replay(nvars, &formula, &steps).unwrap();
    }

    /// The design doc's soundness gate (§4.1): a table missing a row is
    /// incomplete, so the engine may refute a satisfiable formula.  The
    /// verdict is not caught — the table is trusted for it — but the
    /// certificate is: the lemma that row would have blocked does not follow
    /// from the box's source clauses, and no proof is offered.
    #[test]
    fn a_corrupted_table_cannot_be_certified() {
        let k = 4;
        let (nvars, gates, mut boxes) = adder_chain(k);
        for b in &mut boxes {
            let mut rows = b.rows.clone();
            rows.remove(0);                       // drop the all-zero row
            *b = TableBox::new(rows);
        }
        let units = adder_units(k, k, 9);         // 4 + 5 = 9: satisfiable
        let mut e = Engine::new(nvars, boxes);
        for c in &units { e.add_clause(&c.iter().map(|&l| lit_of_dimacs(l)).collect::<Vec<_>>()); }
        e.set_proof(proof::Proof::buffer());
        e.set_box_source(&gates);
        let v = e.solve();
        let p = e.proof.as_ref().expect("proof");
        if v == Verdict::Unsat {
            assert!(p.incomplete.is_some(), "a refutation from a corrupted table was certified");
        }
    }

    /// Without the source clauses a box propagation cannot be derived, so
    /// the proof says so instead of offering an unjustified step.
    #[test]
    fn a_boxed_refutation_without_sources_is_uncertified() {
        let k = 8;
        let (nvars, _gates, boxes) = adder_chain(k);
        let units = adder_units(k, 4, 200);
        let mut e = Engine::new(nvars, boxes);
        for c in &units { e.add_clause(&c.iter().map(|&l| lit_of_dimacs(l)).collect::<Vec<_>>()); }
        e.set_proof(proof::Proof::buffer());
        assert_eq!(e.solve(), Verdict::Unsat);
        assert!(e.proof.as_ref().unwrap().incomplete.is_some());
    }

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
pub mod proof;
pub mod expand;
pub mod controller;
