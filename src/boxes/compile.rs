//! Box compilation: a definition's models — the canonical uncovered paths of
//! its complement — projected onto the interface, as a [`Table`] that can be
//! instantiated into a [`TableBox`] over concrete variables.  Shared by the
//! `box-compile` CLI and the web app's `/boxes/compile` endpoint.
//! Design: `doc/box_backend_design.md` §5.

use std::collections::{HashMap, HashSet};
use super::expand::{atomize_box_calls, family_of, Arg, BoxSig};

use super::TableBox;
use crate::controller::SmartController;
use crate::matrix::{DynOnClass, Lit, Matrix, PathParams, PathsClass};

/// A compiled box: rows in model polarity over `vars` (`None` = don't care).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Table {
    pub name: String,
    /// Interface families in call order (parameters, then exposed families).
    /// Every column belongs to exactly one (`expand::family_of`).
    pub params: Vec<String>,
    /// Columns: the members of each family in turn, in subscript order.
    pub vars: Vec<String>,
    pub rows: Vec<Vec<Option<bool>>>,
    pub formula: String,
    pub internals_projected: Vec<String>,
    pub uncovered_paths: usize,
    /// The rows are a proven minimum cover (exact Quine–McCluskey), not just irredundant.
    pub exact_min: bool,
    /// Milliseconds spent minimizing this table.
    pub minimize_ms: u64,
}

impl Table {
    /// JSON form: rows as `1` / `0` / `null`.
    pub fn to_json(&self) -> serde_json::Value {
        serde_json::json!({
            "name": self.name,
            "params": self.params,
            "vars": self.vars,
            "rows": self.rows.iter().map(|r| r.iter().map(|c| match c {
                Some(true) => serde_json::Value::from(1),
                Some(false) => serde_json::Value::from(0),
                None => serde_json::Value::Null,
            }).collect::<Vec<_>>()).collect::<Vec<_>>(),
            "formula": self.formula,
            "internals_projected": self.internals_projected,
            "uncovered_paths": self.uncovered_paths,
            "exact_min": self.exact_min,
            "minimize_ms": self.minimize_ms,
        })
    }

    /// Parse the JSON form (cells may be `1`/`0`/`null` or `true`/`false`/`null`).
    pub fn from_json(v: &serde_json::Value) -> Result<Table, String> {
        let strs = |key: &str| -> Vec<String> {
            v[key].as_array().map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect()).unwrap_or_default()
        };
        let vars = strs("vars");
        if vars.is_empty() { return Err("table: missing \"vars\"".into()); }
        let params = { let p = strs("params"); if p.is_empty() { vars.clone() } else { p } };
        let rows_v = v["rows"].as_array().ok_or("table: missing \"rows\"")?;
        let mut rows = Vec::with_capacity(rows_v.len());
        for r in rows_v {
            let cells = r.as_array().ok_or("table: row is not an array")?;
            if cells.len() != vars.len() { return Err(format!("table: row has {} cells, expected {}", cells.len(), vars.len())); }
            rows.push(cells.iter().map(|c| match c {
                serde_json::Value::Null => Ok(None),
                serde_json::Value::Bool(b) => Ok(Some(*b)),
                serde_json::Value::Number(n) => match n.as_i64() { Some(1) => Ok(Some(true)), Some(0) => Ok(Some(false)), _ => Err(format!("table: bad cell {c}")) },
                other => Err(format!("table: bad cell {other}")),
            }).collect::<Result<Vec<_>, String>>()?);
        }
        Ok(Table {
            params,
            name: v["name"].as_str().unwrap_or("box").to_string(),
            vars, rows,
            formula: v["formula"].as_str().unwrap_or("").to_string(),
            internals_projected: strs("internals_projected"),
            exact_min: v["exact_min"].as_bool().unwrap_or(false),
            minimize_ms: v["minimize_ms"].as_u64().unwrap_or(0),
            uncovered_paths: v["uncovered_paths"].as_u64().unwrap_or(0) as usize,
        })
    }

    /// Bind the columns to 0-based variables and build the engine's box.
    pub fn instantiate(&self, args: &[u32]) -> Result<TableBox, String> {
        if args.len() != self.vars.len() {
            return Err(format!("{}: expects {} arguments, instance has {}", self.name, self.vars.len(), args.len()));
        }
        let rows = self.rows.iter().map(|r| {
            r.iter().enumerate().filter_map(|(ci, c)| c.map(|b| Lit { var: args[ci], neg: !b })).collect()
        }).collect();
        Ok(TableBox::new(rows))
    }
}


/// How a call binds one table column: to a (possibly complemented) variable
/// of the enclosing problem, or to a constant.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ArgBinding {
    Var { id: u32, neg: bool },
    Const(bool),
}

impl Table {
    /// Rows of this table over the problem's variables, for one call.
    /// A complemented argument flips the column; a constant filters the rows
    /// (and drops the column).
    pub fn instantiate_args(&self, args: &[ArgBinding]) -> Result<Vec<Vec<Lit>>, String> {
        if args.len() != self.vars.len() {
            return Err(format!("{}: expects {} arguments, call has {}", self.name, self.vars.len(), args.len()));
        }
        let mut out = Vec::with_capacity(self.rows.len());
        'rows: for r in &self.rows {
            let mut lits = Vec::new();
            for (ci, c) in r.iter().enumerate() {
                let Some(b) = *c else { continue };
                match args[ci] {
                    ArgBinding::Var { id, neg } => lits.push(Lit { var: id, neg: !(b ^ neg) }),
                    ArgBinding::Const(k) => if k != b { continue 'rows; },
                }
            }
            out.push(lits);
        }
        Ok(out)
    }

    /// The table of the box's negation over the same columns: every full
    /// assignment of the columns matched by no row.  Exact for projected boxes
    /// (¬∃U.B = ∀U.¬B); rows are full assignments (no don't-cares).  Errors when
    /// the column count exceeds `max_cols` (2^k enumeration).
    pub fn complement(&self, max_cols: usize, budget: &MinimizeBudget) -> Result<Table, String> {
        let k = self.vars.len();
        if k > max_cols {
            return Err(format!("{}: negative table needs 2^{k} assignments over {k} columns (limit {max_cols})", self.name));
        }
        let mut rows = Vec::new();
        for a in 0u64..(1u64 << k) {
            let asg: Vec<bool> = (0..k).map(|i| (a >> i) & 1 == 1).collect();
            let covered = self.rows.iter().any(|r| r.iter().zip(&asg).all(|(c, &v)| c.is_none_or(|b| b == v)));
            if !covered { rows.push(asg.iter().map(|&v| Some(v)).collect()); }
        }
        let t0 = std::time::Instant::now();
        let (rows, exact_min) = minimize_rows(rows, k, budget);
        Ok(Table { name: format!("{}'", self.name), params: self.params.clone(), vars: self.vars.clone(), rows, formula: format!("({})'", self.formula),
                   internals_projected: self.internals_projected.clone(), uncovered_paths: 0, exact_min, minimize_ms: t0.elapsed().as_millis() as u64 })
    }
}

/// The table `sel = sel_value ⇒ (one of `rows`)`: every row gets the selector
/// literal, plus one escape row that only fixes the selector to the other
/// value.  With `sel_value = true` this is `atom ⇒ box`; with `false`,
/// `¬atom ⇒ ¬box` when `rows` is the negative table — together they make the
/// atom equivalent to the box (§2.2: two tables per box).
pub fn implication_box(rows: Vec<Vec<Lit>>, sel: u32, sel_value: bool) -> TableBox {
    let mut all: Vec<Vec<Lit>> = Vec::with_capacity(rows.len() + 1);
    all.push(vec![Lit { var: sel, neg: sel_value }]);          // escape: sel ≠ sel_value
    for mut r in rows {
        r.push(Lit { var: sel, neg: !sel_value });               // sel = sel_value
        all.push(r);
    }
    TableBox::new(all)
}


/// Columns up to which tables are minimized (the function is enumerated over
/// 2^k assignments — the same cap as the negative-table complement).
pub const MINIMIZE_MAX_COLS: usize = 20;
/// Minterm visits the EXPAND + IRREDUNDANT heuristic may spend on one table
/// before giving up and keeping the rows as they are.
pub const MINIMIZE_MAX_WORK: u64 = 40_000_000;

/// The assignment indices (bit i = column i) a row with don't-cares covers.
fn cube_minterms(row: &[Option<bool>]) -> Vec<usize> {
    let mut base = 0usize;
    let mut dcs = Vec::new();
    for (i, c) in row.iter().enumerate() {
        match c { Some(true) => base |= 1 << i, Some(false) => {}, None => dcs.push(i) }
    }
    (0..1usize << dcs.len()).map(|m| {
        let mut idx = base;
        for (j, &i) in dcs.iter().enumerate() { if (m >> j) & 1 == 1 { idx |= 1 << i; } }
        idx
    }).collect()
}


/// Columns up to which the exact minimum is computed (Quine–McCluskey primes +
/// an exact cover); above this, or when the work budgets below are exceeded,
/// [`minimize_rows`] falls back to the EXPAND + IRREDUNDANT heuristic.
pub const QM_MAX_COLS: usize = 14;

/// Work budgets for the exact minimization of one table (settable per box:
/// `budget cubes=N ms=M` in the declaration).  Over either, the heuristic
/// cover — which seeds the exact search as its upper bound — is kept.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MinimizeBudget {
    /// Cubes the Quine–McCluskey prime enumeration may generate in total.
    pub max_cubes: usize,
    /// Wall-clock budget for the exact cover search.
    pub time: std::time::Duration,
}
impl Default for MinimizeBudget {
    fn default() -> Self { MinimizeBudget { max_cubes: 2_000_000, time: std::time::Duration::from_millis(1500) } }
}
impl MinimizeBudget {
    pub fn new(max_cubes: Option<usize>, ms: Option<u64>) -> Self {
        let d = Self::default();
        MinimizeBudget { max_cubes: max_cubes.unwrap_or(d.max_cubes), time: ms.map(std::time::Duration::from_millis).unwrap_or(d.time) }
    }
}

/// All prime implicants of the function with minterm set `f` (bit i of an
/// index = column i), as `(value, mask)` cubes — `mask` bits are don't-cares.
/// Quine–McCluskey: merge cubes of equal mask whose values differ in one bit.
fn qm_primes(f: &[bool], k: usize, max_cubes: usize, deadline: std::time::Instant) -> Option<Vec<(u32, u32)>> {
    let mut level: HashSet<(u32, u32)> = (0..f.len()).filter(|&m| f[m]).map(|m| (m as u32, 0u32)).collect();
    let mut primes = Vec::new();
    let mut total = 0usize;
    while !level.is_empty() {
        total += level.len();
        if total > max_cubes || std::time::Instant::now() > deadline { return None; }
        let mut merged: HashSet<(u32, u32)> = HashSet::new();
        let mut next: HashSet<(u32, u32)> = HashSet::new();
        // A cube with bit b = 0 merges with its partner that has bit b = 1
        // (same mask): one hash lookup per (cube, free bit).
        let mut seen = 0usize;
        for &(v, m) in &level {
            seen += 1;
            if seen & 4095 == 0 && std::time::Instant::now() > deadline { return None; }
            for b in 0..k as u32 {
                let bit = 1u32 << b;
                if m & bit != 0 || v & bit != 0 { continue; }
                let partner = (v | bit, m);
                if level.contains(&partner) {
                    next.insert((v, m | bit));
                    merged.insert((v, m)); merged.insert(partner);
                }
            }
        }
        for c in &level { if !merged.contains(c) { primes.push(*c); } }
        level = next;
    }
    Some(primes)
}

// ─── Prime-implicant chart: exact minimum cover ──────────────────────────────
type Bits = Vec<u64>;
fn bits_new(n: usize) -> Bits { vec![0; n.div_ceil(64).max(1)] }
fn bits_set(b: &mut Bits, i: usize) { b[i / 64] |= 1 << (i % 64); }
fn bits_clear(b: &mut Bits, i: usize) { b[i / 64] &= !(1 << (i % 64)); }
fn bits_get(b: &Bits, i: usize) -> bool { b[i / 64] >> (i % 64) & 1 == 1 }
fn bits_and(a: &Bits, b: &Bits) -> Bits { a.iter().zip(b).map(|(x, y)| x & y).collect() }
fn bits_and_not(a: &Bits, b: &Bits) -> Bits { a.iter().zip(b).map(|(x, y)| x & !y).collect() }
fn bits_or_into(a: &mut Bits, b: &Bits) { for (x, y) in a.iter_mut().zip(b) { *x |= y; } }
fn bits_count(a: &Bits) -> usize { a.iter().map(|w| w.count_ones() as usize).sum() }
fn bits_is_zero(a: &Bits) -> bool { a.iter().all(|&w| w == 0) }
fn bits_subset(a: &Bits, b: &Bits) -> bool { a.iter().zip(b).all(|(x, y)| x & !y == 0) }
fn bits_intersects(a: &Bits, b: &Bits) -> bool { a.iter().zip(b).any(|(x, y)| x & y != 0) }
fn bits_ones(a: &Bits) -> Vec<usize> {
    let mut out = Vec::new();
    for (wi, &w) in a.iter().enumerate() { let mut w = w; while w != 0 { out.push(wi * 64 + w.trailing_zeros() as usize); w &= w - 1; } }
    out
}

/// The chart: which minterms each prime covers and which primes cover each
/// minterm, as bitsets, plus the search's time budget.
struct Chart { covers: Vec<Bits>, primes_of: Vec<Bits>, nmin: usize, nprimes: usize, deadline: std::time::Instant, timed_out: bool, nodes: usize }

impl Chart {
    /// Essential primes and prime dominance, to a fixpoint.  Forced primes
    /// are appended to `forced`; `remaining` / `alive` shrink.
    fn reduce(&self, remaining: &mut Bits, alive: &mut Bits, forced: &mut Vec<usize>) {
        loop {
            let mut changed = false;
            let mut ess: Vec<usize> = Vec::new();
            for m in bits_ones(remaining) {
                let pm = bits_and(&self.primes_of[m], alive);
                if bits_count(&pm) == 1 { let p = bits_ones(&pm)[0]; if !ess.contains(&p) { ess.push(p); } }
            }
            if !ess.is_empty() {
                for p in ess { forced.push(p); *remaining = bits_and_not(remaining, &self.covers[p]); bits_clear(alive, p); }
                changed = true;
            }
            if bits_is_zero(remaining) { break; }
            let al = bits_ones(alive);
            if al.len() <= 1500 && std::time::Instant::now() < self.deadline {
                let cov: Vec<Bits> = al.iter().map(|&p| bits_and(&self.covers[p], remaining)).collect();
                let cnt: Vec<usize> = cov.iter().map(bits_count).collect();
                for i in 0..al.len() {
                    let dominated = cnt[i] == 0 || (0..al.len()).any(|j| j != i && bits_subset(&cov[i], &cov[j]) && (cnt[j] > cnt[i] || j < i));
                    if dominated { bits_clear(alive, al[i]); changed = true; }
                }
            }
            if !changed { break; }
        }
    }

    /// Minterm dominance (root only — quadratic in the minterms): a minterm
    /// whose covering primes include another's can be dropped.
    fn minterm_dominance(&self, remaining: &mut Bits, alive: &Bits) {
        let ms = bits_ones(remaining);
        if ms.len() > 2000 || std::time::Instant::now() > self.deadline { return; }
        let pm: Vec<Bits> = ms.iter().map(|&m| bits_and(&self.primes_of[m], alive)).collect();
        let cnt: Vec<usize> = pm.iter().map(bits_count).collect();
        for i in 0..ms.len() {
            if i & 255 == 0 && std::time::Instant::now() > self.deadline { return; }
            if (0..ms.len()).any(|j| j != i && bits_subset(&pm[j], &pm[i]) && (cnt[j] < cnt[i] || j < i)) { bits_clear(remaining, ms[i]); }
        }
    }

    fn greedy(&self, remaining: &Bits, alive: &Bits) -> Vec<usize> {
        let mut rem = remaining.clone(); let mut out = Vec::new();
        let al = bits_ones(alive);
        while !bits_is_zero(&rem) {
            let Some(&p) = al.iter().filter(|&&p| !out.contains(&p)).max_by_key(|&&p| bits_count(&bits_and(&self.covers[p], &rem))) else { break };
            out.push(p); rem = bits_and_not(&rem, &self.covers[p]);
        }
        out
    }

    /// Independent-set lower bound: minterms no two of which share a prime
    /// each need a prime of their own.
    fn lower_bound(&self, remaining: &Bits, alive: &Bits) -> usize {
        let mut ms = bits_ones(remaining);
        ms.sort_by_key(|&m| bits_count(&bits_and(&self.primes_of[m], alive)));
        let mut blocked = bits_new(self.nmin); let mut lb = 0;
        for m in ms {
            if bits_get(&blocked, m) { continue; }
            lb += 1;
            for p in bits_ones(&bits_and(&self.primes_of[m], alive)) { bits_or_into(&mut blocked, &self.covers[p]); }
        }
        lb
    }

    /// Connected components of the chart (minterms linked through primes).
    fn components(&self, remaining: &Bits, alive: &Bits) -> Vec<Bits> {
        let ms = bits_ones(remaining);
        let mut parent: Vec<usize> = (0..self.nmin).collect();
        fn find(parent: &mut [usize], x: usize) -> usize { let mut x = x; while parent[x] != x { parent[x] = parent[parent[x]]; x = parent[x]; } x }
        for p in bits_ones(alive) {
            let ones = bits_ones(&bits_and(&self.covers[p], remaining));
            for w in ones.windows(2) { let (a, b) = (find(&mut parent, w[0]), find(&mut parent, w[1])); if a != b { parent[a] = b; } }
        }
        let mut groups: HashMap<usize, Bits> = HashMap::new();
        for m in ms { bits_set(groups.entry(find(&mut parent, m)).or_insert_with(|| bits_new(self.nmin)), m); }
        groups.into_values().collect()
    }

    fn alive_for(&self, comp: &Bits, alive: &Bits) -> Bits {
        let mut out = bits_new(self.nprimes);
        for p in bits_ones(alive) { if bits_intersects(&self.covers[p], comp) { bits_set(&mut out, p); } }
        out
    }

    /// A cover of `remaining` by `alive` primes of size < `bound`, minimum
    /// among those, or `None` (none exists, or the time budget ran out —
    /// see `timed_out`).
    fn solve(&mut self, remaining: Bits, alive: Bits, bound: usize) -> Option<Vec<usize>> {
        self.solve_at(remaining, alive, bound, 0)
    }

    fn solve_at(&mut self, remaining: Bits, alive: Bits, bound: usize, depth: usize) -> Option<Vec<usize>> {
        self.nodes += 1;
        if std::time::Instant::now() > self.deadline { self.timed_out = true; }
        if self.timed_out || bound == 0 { return None; }
        let (mut remaining, mut alive, mut forced) = (remaining, alive, Vec::new());
        self.reduce(&mut remaining, &mut alive, &mut forced);
        if forced.len() >= bound { return None; }
        if bits_is_zero(&remaining) { return Some(forced); }
        let bound_rest = bound - forced.len();
        let comps = self.components(&remaining, &alive);
        if comps.len() > 1 {
            let alives: Vec<Bits> = comps.iter().map(|c| self.alive_for(c, &alive)).collect();
            let lbs: Vec<usize> = comps.iter().zip(&alives).map(|(c, a)| self.lower_bound(c, a)).collect();
            if lbs.iter().sum::<usize>() >= bound_rest { return None; }
            let mut result = forced; let mut used = 0usize;
            for i in 0..comps.len() {
                let others_lb: usize = lbs[i + 1..].iter().sum();
                if used + others_lb >= bound_rest { return None; }
                let sub = self.solve_at(comps[i].clone(), alives[i].clone(), bound_rest - used - others_lb, depth + 1)?;
                used += sub.len(); result.extend(sub);
            }
            return Some(result);
        }
        let lb = self.lower_bound(&remaining, &alive);
        if lb >= bound_rest { return None; }
        let (mut best, mut bound_rest) = (None, bound_rest);
        // a greedy cover re-seeds the bound at the root and on small remainders
        // (it is the expensive part of a node on large charts)
        if depth == 0 || bits_count(&remaining) <= 256 {
            let g = self.greedy(&remaining, &alive);
            if g.len() < bound_rest { bound_rest = g.len(); best = Some(g); }
        }
        if lb < bound_rest {
            let m = bits_ones(&remaining).into_iter().min_by_key(|&m| bits_count(&bits_and(&self.primes_of[m], &alive))).unwrap();
            let mut ps = bits_ones(&bits_and(&self.primes_of[m], &alive));
            ps.sort_by_key(|&p| std::cmp::Reverse(bits_count(&bits_and(&self.covers[p], &remaining))));
            for p in ps {
                if bound_rest <= 1 { break; }
                let rem = bits_and_not(&remaining, &self.covers[p]);
                let mut al = alive.clone(); bits_clear(&mut al, p);
                if let Some(sub) = self.solve_at(rem, al, bound_rest - 1, depth + 1) { let mut cand = vec![p]; cand.extend(sub); bound_rest = cand.len(); best = Some(cand); }
                if self.timed_out { break; }
            }
        }
        best.map(|b| { let mut r = forced; r.extend(b); r })
    }
}

/// Minimum cover of the prime-implicant chart.  Returns the best cover found
/// (never worse than `initial_best`, if given) and whether it is a proven
/// minimum (the search finished within `time`).
fn exact_cover(primes: &[(u32, u32)], minterms: &[u32], initial_best: Option<Vec<usize>>, deadline: std::time::Instant) -> (Option<Vec<usize>>, bool) {
    let (nmin, nprimes) = (minterms.len(), primes.len());
    let idx_of: HashMap<u32, usize> = minterms.iter().enumerate().map(|(i, &m)| (m, i)).collect();
    let mut covers: Vec<Bits> = vec![bits_new(nmin); nprimes];
    let mut primes_of: Vec<Bits> = vec![bits_new(nprimes); nmin];
    for (p, &(v, m)) in primes.iter().enumerate() {
        for mi in cube_minterms_vm(v, m) { if let Some(&i) = idx_of.get(&mi) { bits_set(&mut covers[p], i); bits_set(&mut primes_of[i], p); } }
    }
    let mut chart = Chart { covers, primes_of, nmin, nprimes, deadline, timed_out: false, nodes: 0 };
    let mut remaining = bits_new(nmin); for i in 0..nmin { bits_set(&mut remaining, i); }
    let mut alive = bits_new(nprimes); for p in 0..nprimes { bits_set(&mut alive, p); }
    // root reductions, then a greedy seed
    let mut forced = Vec::new();
    chart.reduce(&mut remaining, &mut alive, &mut forced);
    chart.minterm_dominance(&mut remaining, &alive);
    let mut best: Option<Vec<usize>> = initial_best;
    let mut seed = forced.clone(); seed.extend(chart.greedy(&remaining, &alive));
    if best.as_ref().is_none_or(|b| seed.len() < b.len()) { best = Some(seed); }
    let bound = best.as_ref().map_or(usize::MAX, |b| b.len());
    if let Some(found) = chart.solve(remaining, alive, bound.saturating_sub(forced.len())) {
        let mut cover = forced; cover.extend(found);
        if best.as_ref().is_none_or(|b| cover.len() < b.len()) { best = Some(cover); }
    }
    (best, !chart.timed_out)
}

/// The assignment indices a `(value, mask)` cube covers.
fn cube_minterms_vm(v: u32, m: u32) -> Vec<u32> {
    let bits: Vec<u32> = (0..32).filter(|&i| m >> i & 1 == 1).collect();
    (0..1u32 << bits.len()).map(|s| { let mut x = v; for (j, &b) in bits.iter().enumerate() { if s >> j & 1 == 1 { x |= 1 << b; } } x }).collect()
}

/// Exact minimum cover for small column counts: Quine–McCluskey primes and an
/// exact cover.  `None` when over budget (the caller falls back to the heuristic).
fn minimize_exact(f: &[bool], k: usize, heuristic: &[Vec<Option<bool>>], budget: &MinimizeBudget) -> Option<(Vec<Vec<Option<bool>>>, bool)> {
    let minterms: Vec<u32> = (0..f.len()).filter(|&m| f[m]).map(|m| m as u32).collect();
    if minterms.is_empty() { return Some((Vec::new(), true)); }
    let deadline = std::time::Instant::now() + budget.time;
    let primes = qm_primes(f, k, budget.max_cubes, deadline)?;
    // the heuristic cover consists of primes: use it as the initial upper bound
    let index: HashMap<(u32, u32), usize> = primes.iter().enumerate().map(|(i, &c)| (c, i)).collect();
    let bound: Option<Vec<usize>> = heuristic.iter().map(|r| {
        let (mut v, mut m) = (0u32, 0u32);
        for (c, x) in r.iter().enumerate() { match x { Some(true) => v |= 1 << c, Some(false) => {}, None => m |= 1 << c } }
        index.get(&(v, m)).copied()
    }).collect();
    // On a timeout the best cover found so far (never worse than the
    // heuristic seed) is still returned, just not as a proven minimum.
    let (chosen, exact) = exact_cover(&primes, &minterms, bound, deadline);
    let chosen = chosen?;
    let mut rows: Vec<Vec<Option<bool>>> = chosen.iter().map(|&i| {
        let (v, m) = primes[i];
        (0..k).map(|c| if m >> c & 1 == 1 { None } else { Some(v >> c & 1 == 1) }).collect()
    }).collect();
    rows.sort();
    Some((rows, exact))
}
/// Minimize a table's rows — a DNF cover with don't-cares — without changing
/// the set of assignments covered.  Up to [`QM_MAX_COLS`] columns the result is
/// a true minimum: Quine–McCluskey prime implicants and an exact cover of the
/// prime-implicant chart ([`minimize_exact`]).  Beyond that, or if the work
/// budgets are exceeded, an irredundant cover by prime implicants: EXPAND grows
/// every row to a maximal cube (a fixed column becomes a don't-care when the
/// flipped half-cube also lies inside the function), then IRREDUNDANT drops
/// rows covered by the others (smallest first).  Row counts then no longer
/// depend on how the definition was written — `lt + eq` and `¬lt(b;a)` compile
/// to the same table — and fewer, wider rows propagate faster.  Rows are
/// returned sorted, with `true` when they are a proven minimum.  Left
/// unchanged when the box has more than [`MINIMIZE_MAX_COLS`] columns.
pub fn minimize_rows(rows: Vec<Vec<Option<bool>>>, k: usize, budget: &MinimizeBudget) -> (Vec<Vec<Option<bool>>>, bool) {
    if k > MINIMIZE_MAX_COLS || rows.is_empty() { return (rows, false); }
    let mut f = vec![false; 1usize << k];
    for r in &rows { for m in cube_minterms(r) { f[m] = true; } }
    // The heuristic enumerates a cube's minterms once per column it tries
    // to free; wide cubes over many columns make that explode (a 9-bit ≤
    // over 18 columns: 10⁹ minterm visits).  Past the work budget the rows
    // are kept as they are — a cover already, just not a small one.
    let mut work: u64 = 0;
    let cost = |c: &[Option<bool>]| 1u64 << c.iter().filter(|x| x.is_none()).count();
    // EXPAND
    let mut cubes: HashSet<Vec<Option<bool>>> = HashSet::new();
    for r in &rows {
        let mut cube = r.clone();
        for c in 0..k {
            if let Some(v) = cube[c] {
                let mut flipped = cube.clone();
                flipped[c] = Some(!v);
                work += cost(&flipped);
                if work > MINIMIZE_MAX_WORK { return (rows, false); }
                if cube_minterms(&flipped).into_iter().all(|m| f[m]) { cube[c] = None; }
            }
        }
        cubes.insert(cube);
    }
    // IRREDUNDANT: smallest cubes first
    let mut cubes: Vec<Vec<Option<bool>>> = cubes.into_iter().collect();
    cubes.sort_by_key(|c| (c.iter().filter(|x| x.is_none()).count(), c.clone()));
    work += 2 * cubes.iter().map(|c| cost(c)).sum::<u64>();
    if work > MINIMIZE_MAX_WORK { return (rows, false); }
    let mut count = vec![0u32; 1usize << k];
    for c in &cubes { for m in cube_minterms(c) { count[m] += 1; } }
    let mut kept = Vec::with_capacity(cubes.len());
    for c in cubes {
        let ms = cube_minterms(&c);
        if ms.iter().all(|&m| count[m] >= 2) { for m in ms { count[m] -= 1; } } else { kept.push(c); }
    }
    kept.sort();
    // exact minimum when small enough and within budget
    if k <= QM_MAX_COLS && let Some((rows, exact)) = minimize_exact(&f, k, &kept, budget) { return (rows, exact); }
    (kept, false)
}

/// Sort key for the members of a family: the bare name first, then integer
/// subscripts numerically (`a_2` before `a_10`, lists lexicographic), then
/// other subscripts alphabetically.
fn subscript_key(name: &str, prefix: &str) -> (u8, Vec<i64>, String) {
    let suffix = name[prefix.len()..].trim_start_matches('_');
    if suffix.is_empty() { return (0, Vec::new(), String::new()); }
    match suffix.split(',').map(|p| p.parse::<i64>()).collect::<Result<Vec<_>, _>>() {
        Ok(nums) => (1, nums, String::new()),
        Err(_) => (2, Vec::new(), suffix.to_string()),
    }
}

/// The interface of a definition over its variables `names`: the families
/// `params ++ expose` (a family is a name prefix, see `expand::family_of`),
/// their member columns in subscript order, and the hidden variables.
pub fn interface_columns(names: &[String], params: &[String], expose: &[String]) -> (Vec<String>, Vec<String>, Vec<String>) {
    let mut families: Vec<String> = params.to_vec();
    for e in expose { if !families.contains(e) { families.push(e.clone()); } }
    let mut cols = Vec::new();
    for (fi, f) in families.iter().enumerate() {
        let mut members: Vec<&String> = names.iter().filter(|n| family_of(n, &families) == Some(fi)).collect();
        members.sort_by_key(|n| subscript_key(n, f));
        cols.extend(members.into_iter().cloned());
    }
    let hidden = names.iter().filter(|n| family_of(n, &families).is_none()).cloned().collect();
    (families, cols, hidden)
}

/// Compile a definition into its table over the interface `params ++ expose`
/// (families of variables — see [`interface_columns`]): enumerate the
/// uncovered paths of the complement, decode each to model polarity, project
/// onto the interface columns (every other variable is hidden — ∃), dedup,
/// and minimize ([`minimize_rows`]).  Must run inside a tokio runtime; errors
/// if more than `max_uncovered_paths` paths are found.
pub async fn compile_box(name: &str, formula: &str, params: &[String], expose: &[String], max_uncovered_paths: usize, budget: &MinimizeBudget) -> Result<Table, String> {
    compile_box_polarity(name, formula, params, expose, max_uncovered_paths, false, budget).await
}

/// Like [`compile_box`]; with `negate` the table of the *complement* of the
/// definition is compiled (its uncovered paths are those of the definition's
/// own NNF).  Only exact when nothing is projected: ¬(∃U.B) ≠ ∃U.¬B — use
/// [`Table::complement`] for a box with projected internals.
pub async fn compile_box_polarity(name: &str, formula: &str, params: &[String], expose: &[String], max_uncovered_paths: usize, negate: bool, budget: &MinimizeBudget) -> Result<Table, String> {
    let (names, nnf) = {
        let m = Matrix::try_from(formula.trim()).map_err(|e| format!("{name}: parse error: {e}"))?;
        (m.ast.vars.clone(), if negate { m.nnf.clone() } else { m.nnf_complement.clone() })
    };
    let (families, cols, internals) = interface_columns(&names, params, expose);
    let col_of: HashMap<String, usize> = cols.iter().enumerate().map(|(i, c)| (c.clone(), i)).collect();
    let params = Some(PathParams {
        paths_class_limit: usize::MAX / 2, uncovered_path_limit: max_uncovered_paths, ..Default::default()
    });
    let nnf_for_builder = nnf.clone();
    let (handle, mut rx, _cancel) = nnf.classify_paths_uncovered_only(
        64,
        move |tx: tokio::sync::mpsc::Sender<(PathsClass, bool)>| {
            let on_class: DynOnClass =
                Box::new(move |class, hit_limit| tx.blocking_send((class, hit_limit)).is_ok());
            SmartController::for_nnf(&nnf_for_builder, params, on_class)
        },
    );
    let mut set: HashSet<Vec<Option<bool>>> = HashSet::new();
    let (mut n, mut hit) = (0usize, false);
    while let Some((class, hit_limit)) = rx.recv().await {
        if hit_limit { hit = true; }
        if let PathsClass::Uncovered(up) = class {
            n += 1;
            // A path literal is made FALSE by the model (§2.2): model value = l.neg.
            let mut row = vec![None; cols.len()];
            for l in &up.lits {
                if let Some(&ci) = col_of.get(&names[l.var as usize]) { row[ci] = Some(l.neg); }
            }
            set.insert(row);
        }
    }
    let _ = handle.await;
    if hit {
        return Err(format!("{name}: more than {max_uncovered_paths} uncovered paths — raise the limit or split the box"));
    }
    let t0 = std::time::Instant::now();
    let (rows, exact_min) = minimize_rows(set.into_iter().collect(), cols.len(), budget);
    Ok(Table {
        name: name.to_string(), params: families, vars: cols, rows,
        formula: formula.trim().to_string(), internals_projected: internals, uncovered_paths: n, exact_min,
        minimize_ms: t0.elapsed().as_millis() as u64,
    })
}


/// Rows a definition may reach while being composed before it is declared
/// too large for composition (the caller falls back to path enumeration).
pub const COMPOSE_MAX_ROWS: usize = 200_000;

/// Compile a definition that is a conjunction of box calls (and literals) by
/// **composition**: instantiate each callee's table over the definition's
/// variables, join the tables one by one, and project every hidden variable
/// as soon as no later conjunct mentions it.  This never looks at the
/// expanded matrix, so a long chain of boxes (a bounded-model-checking
/// unrolling) compiles in milliseconds to a table over its interface only —
/// where a single table carries what per-step propagation cannot.  `lookup`
/// gives a callee's signature and positive table.  Errors when the
/// definition is not such a conjunction (negated or disjoined calls) or grows
/// past [`COMPOSE_MAX_ROWS`]; the caller then falls back to [`compile_box`].
pub fn compile_box_by_join(
    name: &str, formula: &str, params: &[String], expose: &[String],
    lookup: &dyn Fn(&str) -> Option<(BoxSig, Table)>, budget: &MinimizeBudget,
) -> Result<Table, String> {
    let at = atomize_box_calls(formula, &|n| lookup(n).map(|(sig, _)| sig))?;
    if at.calls.is_empty() { return Err(format!("{name}: no box calls to compose")); }
    let m = Matrix::try_from(at.text.trim()).map_err(|e| format!("{name}: parse error: {e}"))?;
    let lits: Vec<Lit> = match &m.nnf {
        crate::matrix::NNF::Lit(l) => vec![l.clone()],
        crate::matrix::NNF::Prod(ch) => ch.iter().map(|c| match c { crate::matrix::NNF::Lit(l) => Ok(l.clone()), _ => Err(()) })
            .collect::<Result<Vec<_>, ()>>().map_err(|_| format!("{name}: not a conjunction of box calls and literals"))?,
        _ => return Err(format!("{name}: not a conjunction of box calls and literals")),
    };
    let atom_index: HashMap<&str, usize> = at.calls.iter().enumerate().map(|(i, c)| (c.atom.as_str(), i)).collect();
    // the variable universe: residual literals and every column of every call
    let mut names: Vec<String> = Vec::new();
    let mut index: HashMap<String, usize> = HashMap::new();
    let id = |n: &str, names: &mut Vec<String>, index: &mut HashMap<String, usize>| -> usize {
        if let Some(&i) = index.get(n) { i } else { names.push(n.to_string()); index.insert(n.to_string(), names.len() - 1); names.len() - 1 }
    };
    let mut residual: Vec<(usize, bool)> = Vec::new();
    for l in &lits {
        let vname = &m.ast.vars[l.var as usize];
        if let Some(&ci) = atom_index.get(vname.as_str()) {
            if l.neg { return Err(format!("{name}: call {} is negated — not composable", at.calls[ci].label)); }
        } else {
            let i = id(vname, &mut names, &mut index);
            residual.push((i, !l.neg));
        }
    }
    // per call: the callee's rows over universe columns (constants filter rows)
    struct CallRows { cols: Vec<usize>, rows: Vec<Vec<Option<bool>>> }
    let mut calls: Vec<CallRows> = Vec::new();
    for c in &at.calls {
        let (sig, table) = lookup(&c.name).ok_or_else(|| format!("{name}: unknown box `{}`", c.name))?;
        let _ = sig;
        let mut colmap: Vec<Option<(usize, bool)>> = Vec::with_capacity(table.vars.len());   // None = constant column
        let mut consts: Vec<Option<bool>> = Vec::with_capacity(table.vars.len());
        for col in &table.vars {
            let fi = family_of(col, &table.params).ok_or_else(|| format!("{}: column {col} belongs to no parameter", table.name))?;
            match &c.args[fi] {
                Arg::Const(b) => { colmap.push(None); consts.push(Some(*b)); }
                Arg::Var { name: an, neg } => {
                    let global = format!("{an}{}", &col[table.params[fi].len()..]);
                    colmap.push(Some((id(&global, &mut names, &mut index), *neg))); consts.push(None);
                }
            }
        }
        let mut rows = Vec::with_capacity(table.rows.len());
        'rows: for r in &table.rows {
            let mut row: Vec<(usize, bool)> = Vec::new();
            for (ci, cell) in r.iter().enumerate() {
                let Some(v) = *cell else { continue };
                match colmap[ci] {
                    None => if consts[ci] != Some(v) { continue 'rows; },
                    Some((gi, neg)) => row.push((gi, v ^ neg)),
                }
            }
            rows.push(row);
        }
        let cols: Vec<usize> = colmap.iter().filter_map(|c| c.map(|(gi, _)| gi)).collect();
        // rows as sparse (col, value) lists → dense later once the universe is known
        calls.push(CallRows { cols, rows: rows.into_iter().map(|r| r.into_iter().collect::<Vec<_>>())
            .map(|r: Vec<(usize, bool)>| { let mut d: Vec<Option<bool>> = Vec::new(); for (gi, v) in r { if d.len() <= gi { d.resize(gi + 1, None); } d[gi] = Some(v); } d }).collect() });
    }
    let width = names.len();
    let widen = |r: &Vec<Option<bool>>| { let mut d = r.clone(); d.resize(width, None); d };
    // interface families and which universe columns are hidden
    let mut families: Vec<String> = params.to_vec();
    for e in expose { if !families.contains(e) { families.push(e.clone()); } }
    let hidden: Vec<bool> = names.iter().map(|n| family_of(n, &families).is_none()).collect();
    // last conjunct mentioning each column (residual counts as conjunct 0)
    let mut last_use: Vec<usize> = vec![0; width];
    for (k, c) in calls.iter().enumerate() { for &gi in &c.cols { last_use[gi] = k + 1; } }
    // start: one row with the residual literals
    let mut acc: Vec<Vec<Option<bool>>> = vec![vec![None; width]];
    for &(i, v) in &residual { acc[0][i] = Some(v); }
    for (k, c) in calls.iter().enumerate() {
        let mut next: HashSet<Vec<Option<bool>>> = HashSet::new();
        for a in &acc {
            for r in &c.rows {
                let r = widen(r);
                let mut merged = a.clone(); let mut ok = true;
                for gi in 0..width {
                    match (a[gi], r[gi]) {
                        (Some(x), Some(y)) if x != y => { ok = false; break; }
                        (None, Some(y)) => merged[gi] = Some(y),
                        _ => {}
                    }
                }
                if ok {
                    // project hidden columns nothing later mentions
                    for gi in 0..width { if hidden[gi] && last_use[gi] <= k + 1 { merged[gi] = None; } }
                    next.insert(merged);
                    if next.len() > COMPOSE_MAX_ROWS { return Err(format!("{name}: composition exceeds {COMPOSE_MAX_ROWS} rows")); }
                }
            }
        }
        acc = next.into_iter().collect();
        if acc.is_empty() { break; }   // the definition is unsatisfiable: an empty table
    }
    // final table over the interface columns, in family order
    let iface_names: Vec<String> = names.iter().filter(|n| family_of(n, &families).is_some()).cloned().collect();
    let (fams, cols, _) = interface_columns(&iface_names, params, expose);
    let col_ids: Vec<usize> = cols.iter().map(|c| index[c]).collect();
    let rows_set: HashSet<Vec<Option<bool>>> = acc.iter().map(|r| col_ids.iter().map(|&gi| r[gi]).collect()).collect();
    let t0 = std::time::Instant::now();
    let (rows, exact_min) = minimize_rows(rows_set.into_iter().collect(), cols.len(), budget);
    let internals: Vec<String> = names.iter().enumerate().filter(|(gi, _)| hidden[*gi]).map(|(_, n)| n.clone()).collect();
    Ok(Table { name: name.to_string(), params: fams, vars: cols, rows, formula: formula.trim().to_string(),
               internals_projected: internals, uncovered_paths: 0, exact_min, minimize_ms: t0.elapsed().as_millis() as u64 })
}
/// [`compile_box`] on a private runtime, for command-line use.
pub fn compile_box_blocking(name: &str, formula: &str, params: &[String], expose: &[String], max_uncovered_paths: usize, budget: &MinimizeBudget) -> Result<Table, String> {
    let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build().map_err(|e| e.to_string())?;
    rt.block_on(compile_box(name, formula, params, expose, max_uncovered_paths, budget))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn adder_compiles_to_its_truth_table() {
        let cols: Vec<String> = ["X", "Y", "C1", "Z", "C"].map(String::from).to_vec();
        let t = compile_box_blocking("full_adder", "(C = X Y + (X ⊕ Y) C1) (Z = X ⊕ Y ⊕ C1)", &cols, &[], 100_000, &MinimizeBudget::default()).unwrap();
        assert_eq!(t.rows.len(), 8);
        for r in &t.rows {
            let v = |i: usize| r[i].unwrap() as u32;
            assert_eq!(v(3), (v(0) + v(1) + v(2)) & 1);          // Z = sum bit
            assert_eq!(v(4), ((v(0) + v(1) + v(2)) >> 1) & 1);   // C = carry
        }
        let back = Table::from_json(&t.to_json()).unwrap();
        assert_eq!(back, t);
        let b = t.instantiate(&[0, 1, 2, 3, 4]).unwrap();
        assert_eq!(b.rows.len(), 8);
        assert!(t.instantiate(&[0, 1]).is_err());
    }

    #[test]
    fn projection_drops_internals() {
        let cols: Vec<String> = ["X", "Y", "C1", "Z", "C"].map(String::from).to_vec();
        let five = "(U1 = X Y) (U2 = U3 C1) (C = U1+U2) (U3 = X ⊕ Y) (Z = U3 ⊕ C1)";
        let t = compile_box_blocking("adder", five, &cols, &[], 100_000, &MinimizeBudget::default()).unwrap();
        assert_eq!(t.internals_projected, ["U1", "U2", "U3"].map(String::from).to_vec());
        let two = compile_box_blocking("full_adder", "(C = X Y + (X ⊕ Y) C1) (Z = X ⊕ Y ⊕ C1)", &cols, &[], 100_000, &MinimizeBudget::default()).unwrap();
        assert_eq!(t.rows, two.rows, "∃U.adder == full_adder as tables");
    }

    #[test]
    fn arg_bindings_constants_and_complement() {
        let t = Table { name: "and".into(), params: vec!["a".into(), "b".into(), "z".into()], vars: vec!["a".into(), "b".into(), "z".into()],
            rows: vec![vec![Some(true), Some(true), Some(true)], vec![Some(false), None, Some(false)], vec![None, Some(false), Some(false)]],
            formula: "z = a b".into(), internals_projected: vec![], uncovered_paths: 3, exact_min: false, minimize_ms: 0 };
        // z = a b with a := x', b := 1, z := y  →  y = x'
        let rows = t.instantiate_args(&[ArgBinding::Var { id: 0, neg: true }, ArgBinding::Const(true), ArgBinding::Var { id: 1, neg: false }]).unwrap();
        assert_eq!(rows, vec![
            vec![Lit { var: 0, neg: true }, Lit { var: 1, neg: false }],   // a=1 ⇒ x=0, z=1
            vec![Lit { var: 0, neg: false }, Lit { var: 1, neg: true }],   // a=0 ⇒ x=1, z=0
        ]);                                                                 // row 3 (b=0) filtered by b := 1
        let c = t.complement(8, &MinimizeBudget::default()).unwrap();
        // z = a b has 4 non-models of (a,b,z); minimized to the 3 primes (0,-,1), (-,0,1), (1,1,0)
        assert_eq!(c.rows.len(), 3);
        assert!(c.rows.iter().all(|r| cube_minterms(r).into_iter().all(|m| { let (a, b, z) = (m & 1 == 1, m & 2 == 2, m & 4 == 4); z != (a && b) })));
        // atom ⇒ box: the escape row plus each row tagged with the atom
        let ib = implication_box(rows.clone(), 5, true);
        assert_eq!(ib.rows.len(), 3);
        let mut e = crate::boxes::Engine::new(6, vec![ib, TableBox::clause(&[6]), TableBox::clause(&[1])]);   // atom=true, x=true ⇒ y=false
        match e.solve() { crate::boxes::Verdict::Sat(m) => assert!(!m[1]), v => panic!("{v:?}") }
    }

    #[test]
    fn families_group_subscripted_variables_and_hide_the_rest() {
        let (fam, cols, hidden) = interface_columns(
            &["b_10", "a_2", "a_0", "c_1", "a", "b_1"].map(String::from), &["a".into(), "b".into()], &[]);
        assert_eq!(fam, ["a", "b"].map(String::from).to_vec());
        assert_eq!(cols, ["a", "a_0", "a_2", "b_1", "b_10"].map(String::from).to_vec());   // numeric subscript order
        assert_eq!(hidden, vec!["c_1".to_string()]);
        // a 2-bit equality box: 4 columns, 4 rows
        let t = compile_box_blocking("eq2", "(a_0 = b_0) (a_1 = b_1)", &["a".into(), "b".into()], &[], 100_000, &MinimizeBudget::default()).unwrap();
        assert_eq!(t.params, ["a", "b"].map(String::from).to_vec());
        assert_eq!(t.vars, ["a_0", "a_1", "b_0", "b_1"].map(String::from).to_vec());
        assert_eq!(t.rows.len(), 4);
        // a carry family c_* is hidden unless exposed
        let f = "(c_1 = a_0 b_0) (s_0 = a_0 ⊕ b_0) (s_1 = c_1 ⊕ a_1 ⊕ b_1)";
        let h = compile_box_blocking("half2", f, &["a".into(), "b".into(), "s".into()], &[], 100_000, &MinimizeBudget::default()).unwrap();
        assert_eq!(h.internals_projected, vec!["c_1".to_string()]);
        assert_eq!(h.vars, ["a_0", "a_1", "b_0", "b_1", "s_0", "s_1"].map(String::from).to_vec());
        assert_eq!(h.rows.len(), 16);
        let e = compile_box_blocking("half2", f, &["a".into(), "b".into(), "s".into()], &["c".into()], 100_000, &MinimizeBudget::default()).unwrap();
        assert_eq!(e.params, ["a", "b", "s", "c"].map(String::from).to_vec());
        assert_eq!(e.vars.last().map(String::as_str), Some("c_1"));
        assert!(e.internals_projected.is_empty());
        let j = e.to_json(); let back = Table::from_json(&j).unwrap();
        assert_eq!(back.params, e.params);
    }

    #[test]
    fn minimization_is_exact_and_formula_independent() {
        // Coverage is preserved and every kept row is a prime implicant.
        let rows = vec![vec![Some(false), Some(false)], vec![Some(false), Some(true)], vec![Some(true), Some(true)]];
        let (m, exact) = minimize_rows(rows.clone(), 2, &MinimizeBudget::default());
        assert!(exact);
        let cover = |rs: &Vec<Vec<Option<bool>>>| { let mut v: Vec<usize> = rs.iter().flat_map(|r| cube_minterms(r)).collect(); v.sort(); v.dedup(); v };
        assert_eq!(cover(&m), cover(&rows));
        assert_eq!(m, vec![vec![None, Some(true)], vec![Some(false), None]]);   // b + a' (sorted)
        // a ≤ b over 4-bit vectors has 23 prime implicants, all essential: the
        // minimum cover is 23 rows however the relation is written — as
        // lt + eq, or as the negation of lt(b; a).
        let lt = |a: &str, b: &str| -> String {
            (0..4).rev().map(|i| {
                let mut t: Vec<String> = ((i + 1)..4).map(|j| format!("({a}_{j} = {b}_{j})")).collect();
                t.push(format!("{a}_{i}' {b}_{i}"));
                t.join(" ")
            }).collect::<Vec<_>>().join(" + ")
        };
        let eq: String = (0..4).map(|i| format!("(a_{i} = b_{i})")).collect::<Vec<_>>().join(" ");
        let le = format!("{} + {}", lt("a", "b"), eq);
        let ab = ["a".to_string(), "b".to_string()];
        let le_t = compile_box_blocking("le4", &le, &ab, &[], 100_000, &MinimizeBudget::default()).unwrap();
        assert_eq!(le_t.rows.len(), 23);
        let rt = tokio::runtime::Builder::new_multi_thread().enable_all().build().unwrap();
        let lt_ba_neg = rt.block_on(compile_box_polarity("lt4", &lt("b", "a"), &ab, &[], 100_000, true, &MinimizeBudget::default())).unwrap();
        assert_eq!(lt_ba_neg.rows.len(), 23);
        assert_eq!(cover(&le_t.rows), cover(&lt_ba_neg.rows));   // the same 136 assignments
        assert_eq!(cover(&le_t.rows).len(), 136);
    }

    #[test]
    fn exact_minimum_on_a_cyclic_cover() {
        // f(a,b,c) = Σm(0,1,2,5,6,7): six primes of two minterms each, none
        // essential; an irredundant cover can have 4 rows, the minimum is 3.
        let bits = |m: usize| (0..3).map(|i| Some(m >> i & 1 == 1)).collect::<Vec<_>>();
        let rows: Vec<Vec<Option<bool>>> = [0usize, 1, 2, 5, 6, 7].iter().map(|&m| bits(m)).collect();
        let (m, exact) = minimize_rows(rows.clone(), 3, &MinimizeBudget::default());
        assert!(exact);
        assert_eq!(m.len(), 3, "{m:?}");

        let cover = |rs: &Vec<Vec<Option<bool>>>| { let mut v: Vec<usize> = rs.iter().flat_map(|r| cube_minterms(r)).collect(); v.sort(); v.dedup(); v };
        assert_eq!(cover(&m), vec![0, 1, 2, 5, 6, 7]);
        // an exhausted cube budget keeps the (irredundant) heuristic cover
        let (h, exact) = minimize_rows(rows.clone(), 3, &MinimizeBudget::new(Some(1), None));
        assert!(!exact);
        assert_eq!(cover(&h), vec![0, 1, 2, 5, 6, 7]);
        // the heuristic path (above QM_MAX_COLS) still preserves coverage
        let k = QM_MAX_COLS + 1;
        let wide: Vec<Vec<Option<bool>>> = (0..4).map(|j| (0..k).map(|c| if c < 2 { Some(j >> c & 1 == 1) } else if c == 2 { Some(true) } else { None }).collect()).collect();
        let (w, exact) = minimize_rows(wide.clone(), k, &MinimizeBudget::default());
        assert!(!exact);
        assert_eq!(w.len(), 1);                                   // the four rows merge into one cube
        assert_eq!(cover(&w), cover(&wide));
    }

    #[test]
    fn exact_cover_decomposes_independent_charts() {
        // f = x0 x1 + x2 x3 + x4 x5: three primes on disjoint variables — the
        // chart splits into three components, each covered by its prime.
        let mut rows = Vec::new();
        for m in 0..64usize { if (m & 3) == 3 || (m >> 2 & 3) == 3 || (m >> 4 & 3) == 3 { rows.push((0..6).map(|i| Some(m >> i & 1 == 1)).collect::<Vec<_>>()); } }
        let (r, exact) = minimize_rows(rows, 6, &MinimizeBudget::default());
        assert!(exact);
        assert_eq!(r.len(), 3);
        assert!(r.iter().all(|row| row.iter().filter(|c| c.is_some()).count() == 2));
    }

    #[test]
    fn composition_joins_tables_and_projects_the_chain() {
        // inc(c; d): d = c + 1 over 2 bits, no overflow — 3 rows over c_0,c_1,d_0,d_1
        let inc = compile_box_blocking("inc", "(d_0 = c_0') (d_1 = c_1 ⊕ c_0) (c_0 c_1)'", &["c".into(), "d".into()], &[], 1000, &MinimizeBudget::default()).unwrap();
        assert_eq!(inc.rows.len(), 3);
        let lookup = |n: &str| if n == "inc" { Some((BoxSig { params: inc.params.clone(), internals: vec![], formula: inc.formula.clone() }, inc.clone())) } else { None };
        // chain2(c0; c2) := inc(c0; c1) inc(c1; c2), c1 hidden: c2 = c0 + 2 → rows (0,2), (1,3)
        let t = compile_box_by_join("chain2", "inc(c0; c1) inc(c1; c2)", &["c0".into(), "c2".into()], &[], &lookup, &MinimizeBudget::default()).unwrap();
        assert_eq!(t.vars, ["c0_0", "c0_1", "c2_0", "c2_1"].map(String::from).to_vec());
        assert_eq!(t.internals_projected, ["c1_0", "c1_1"].map(String::from).to_vec());
        let mut rows = t.rows.clone(); rows.sort();
        assert_eq!(rows, vec![vec![Some(false), Some(false), Some(false), Some(true)], vec![Some(true), Some(false), Some(true), Some(true)]]);
        // a residual literal joins in; a negated call is refused
        let t2 = compile_box_by_join("chain2b", "inc(c0; c1) inc(c1; c2) c0_0", &["c0".into(), "c2".into()], &[], &lookup, &MinimizeBudget::default()).unwrap();
        assert_eq!(t2.rows.len(), 1);
        assert!(compile_box_by_join("bad", "inc(c0; c1)' inc(c1; c2)", &["c0".into(), "c2".into()], &[], &lookup, &MinimizeBudget::default()).is_err());
    }
}
