//! Multiplier recogniser and numeric factoring — hydra's factoring tactic.
//!
//! A factoring instance (ezfact, pyhala-braun) is a multiplier circuit
//! `out = a · b` with the output bits pinned by unit clauses to a number N
//! and the factor bits free.  The recogniser reads the circuit's structure
//! from the clauses and its conventions from the circuit's own behaviour:
//!
//! 1. Structure.  Parity relations (a 3- or 4-variable set carrying every
//!    clause of one parity) are the sum cells; union-find over their
//!    unpinned members gives the product columns.  The factor bits are the
//!    unpinned variables in no relation that meet at least four others in
//!    gate clauses (the 4-core of the co-occurrence graph — a factor bit
//!    meets every bit of the other factor in its partial-product gates), a
//!    bipartite split separates the two factors, and the addition table
//!    (which pairs meet in which column) labels the bits by weight from an
//!    end.  Each factor bit's polarity is read off its AND gates: a shuffled
//!    instance flips every variable independently.
//! 2. Reading.  48 random factor assignments are propagated through the
//!    pin-free CNF (leniently: a falsified clause is counted, not fatal).
//!    Pins the factor bits never determine and that add no falsified clause
//!    are the circuit's constants and stay pinned; pins that never vary are
//!    side constraints (pyhala-braun's "the factor is not 1"); every other
//!    pin, and every clause group some probe violates (a gate whose output
//!    was folded into a constant), is matched against the bits of the
//!    product under each reading of the factor bits — orientation of the
//!    labelling and an implicit odd low bit per factor.  A reading that
//!    leaves at most a few bits of N unread fixes N (the unread bits are
//!    enumerated).
//! 3. Numbers.  Pollard–Brent with Miller–Rabin on N; every divisor pair of
//!    the circuit's widths is tried by propagation through the *full* CNF
//!    (pins and side constraints included), which also validates the
//!    recognition — a model is checked against every clause.
//!
//! Anything that does not fit falls through (`NotRecognised`).  A number
//! with no fitting pair is `NoFactorPair`: a numeric UNSAT the caller must
//! not report as proven — it hands the instance to a proof-producing
//! solver.  toughsat instances are not recognised: their product bits are
//! folded into the last cells as constants, which unit propagation reads
//! backwards, so a probe violates clauses all over the circuit.

use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::{One, Zero};

/// What the tactic found.
#[derive(Debug, Clone)]
pub enum Tactic {
    /// A model of the whole CNF (index = variable − 1).
    Sat { model: Vec<bool>, info: Multiplier },
    /// The circuit is a multiplier of N and no factor pair fits: unsatisfiable,
    /// but without a proof.
    NoFactorPair { info: Multiplier },
    NotRecognised(String),
}

/// The recognised circuit: the factor bits (LSB first), the output bits
/// (LSB first) and the pinned number.
#[derive(Debug, Clone)]
pub struct Multiplier {
    pub a: Vec<i32>,
    pub b: Vec<i32>,
    pub out: Vec<i32>,
    pub n: BigUint,
}

impl Multiplier {
    pub fn describe(&self) -> String {
        format!("{}×{}-bit multiplier, {} output bits, N = {} ({} bits)", self.a.len(), self.b.len(), self.out.len(), self.n, self.n.bits())
    }
}

// ─── a small two-watched-literal propagator (DIMACS literals) ──────────

struct Bcp {
    clauses: Vec<Vec<i32>>,
    /// per literal code (2·(v−1) + neg): clauses watching it
    watches: Vec<Vec<u32>>,
    /// per variable: None / Some(value)
    val: Vec<Option<bool>>,
    trail: Vec<i32>,
    qhead: usize,
    /// Lenient: a falsified clause is counted, not fatal — propagation goes
    /// on, so a probe evaluates the whole circuit (a folded output cell is
    /// simply violated when its bit disagrees).
    lenient: bool,
    conflicts: usize,
}

#[inline] fn code(l: i32) -> usize { 2 * (l.unsigned_abs() as usize - 1) + (l < 0) as usize }

impl Bcp {
    fn new(nvars: usize, clauses: &[Vec<i32>]) -> Bcp {
        let mut b = Bcp { clauses: Vec::new(), watches: vec![Vec::new(); 2 * nvars], val: vec![None; nvars], trail: Vec::new(), qhead: 0, lenient: false, conflicts: 0 };
        for c in clauses {
            if c.len() >= 2 {
                let ci = b.clauses.len() as u32;
                b.watches[code(c[0]) ^ 1].push(ci);   // watched when it becomes false, i.e. its negation true
                b.watches[code(c[1]) ^ 1].push(ci);
                b.clauses.push(c.clone());
            }
        }
        b
    }
    #[inline] fn lit_val(&self, l: i32) -> Option<bool> { self.val[l.unsigned_abs() as usize - 1].map(|v| v == (l > 0)) }
    fn reset(&mut self) { for &l in &self.trail { self.val[l.unsigned_abs() as usize - 1] = None; } self.trail.clear(); self.qhead = 0; self.conflicts = 0; }
    /// Assign `l` (true) and propagate; false on conflict (in lenient mode
    /// conflicts are counted and propagation continues; false if any so far).
    fn assign(&mut self, l: i32) -> bool {
        match self.lit_val(l) { Some(true) => return self.conflicts == 0, Some(false) => { self.conflicts += 1; return false }, None => {} }
        self.val[l.unsigned_abs() as usize - 1] = Some(l > 0);
        self.trail.push(l);
        self.propagate()
    }
    fn propagate(&mut self) -> bool {
        while self.qhead < self.trail.len() {
            let t = self.trail[self.qhead]; self.qhead += 1;
            // clauses watching the literal ¬t (now false) are indexed by code(t)
            let ws = std::mem::take(&mut self.watches[code(t)]);
            let mut keep = Vec::with_capacity(ws.len());
            let mut conflict = false;
            for (i, &ci) in ws.iter().enumerate() {
                if conflict { keep.push(ci); continue; }
                let c = &mut self.clauses[ci as usize];
                let falselit = -t;
                if c[0] == falselit { c.swap(0, 1); }
                let other = c[0];
                if self.val[other.unsigned_abs() as usize - 1] == Some(other > 0) { keep.push(ci); continue; }
                let mut moved = false;
                for k in 2..c.len() {
                    let l = c[k];
                    if self.val[l.unsigned_abs() as usize - 1] != Some(l < 0) {   // not false
                        c.swap(1, k);
                        let w = c[1];
                        self.watches[code(w) ^ 1].push(ci);
                        moved = true; break;
                    }
                }
                if moved { continue; }
                keep.push(ci);
                match self.val[other.unsigned_abs() as usize - 1] {
                    Some(v) if v == (other > 0) => {}
                    Some(_) if self.lenient => { self.conflicts += 1; }
                    Some(_) => { conflict = true; for &cj in &ws[i + 1..] { keep.push(cj); } break; }
                    None => { self.val[other.unsigned_abs() as usize - 1] = Some(other > 0); self.trail.push(other); }
                }
            }
            self.watches[code(t)] = keep;
            if conflict { self.conflicts += 1; return false; }
        }
        self.conflicts == 0
    }
    fn model(&self) -> Vec<bool> { self.val.iter().map(|v| v.unwrap_or(false)).collect() }
}

// ─── numeric factoring ──────────────────────────────────────────────────

fn mulmod(a: &BigUint, b: &BigUint, m: &BigUint) -> BigUint { (a * b) % m }

fn is_probable_prime(n: &BigUint) -> bool {
    if *n < BigUint::from(2u32) { return false; }
    for p in [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let bp = BigUint::from(p);
        if *n == bp { return true; }
        if (n % &bp).is_zero() { return false; }
    }
    let one = BigUint::one();
    let nm1 = n - &one;
    let s = nm1.trailing_zeros().unwrap_or(0);
    let d = &nm1 >> s;
    'witness: for a in [2u32, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        let mut x = BigUint::from(a).modpow(&d, n);
        if x == one || x == nm1 { continue; }
        for _ in 1..s {
            x = mulmod(&x, &x, n);
            if x == nm1 { continue 'witness; }
        }
        return false;
    }
    true
}

/// Pollard–Brent; `None` when the iteration budget runs out.
fn pollard_brent(n: &BigUint, budget: &mut u64) -> Option<BigUint> {
    if n.is_even() { return Some(BigUint::from(2u32)); }
    let one = BigUint::one();
    let mut c = BigUint::from(1u32);
    loop {
        let mut y = BigUint::from(2u32);
        let m = 128u64;
        let (mut g, mut r, mut q) = (one.clone(), 1u64, one.clone());
        let (mut x, mut ys) = (y.clone(), y.clone());
        while g == one {
            x = y.clone();
            for _ in 0..r { y = (mulmod(&y, &y, n) + &c) % n; }
            let mut k = 0u64;
            while k < r && g == one {
                ys = y.clone();
                let lim = m.min(r - k);
                for _ in 0..lim {
                    y = (mulmod(&y, &y, n) + &c) % n;
                    let diff = if x > y { &x - &y } else { &y - &x };
                    q = mulmod(&q, &diff, n);
                }
                g = q.gcd(n);
                k += lim;
                *budget = budget.saturating_sub(lim);
                if *budget == 0 { return None; }
            }
            r *= 2;
        }
        if g == *n {
            loop {
                ys = (mulmod(&ys, &ys, n) + &c) % n;
                let diff = if x > ys { &x - &ys } else { &ys - &x };
                g = diff.gcd(n);
                if g != one { break; }
                *budget = budget.saturating_sub(1);
                if *budget == 0 { return None; }
            }
        }
        if g != *n { return Some(g); }
        c += 1u32;   // a cycle that failed: another polynomial
        if c > BigUint::from(20u32) { return None; }
    }
}

/// Prime factorisation with multiplicity; `None` on budget exhaustion.
pub fn factorize(n: &BigUint, mut budget: u64) -> Option<Vec<BigUint>> {
    let mut out = Vec::new();
    let mut stack = vec![n.clone()];
    while let Some(m) = stack.pop() {
        if m.is_one() { continue; }
        if is_probable_prime(&m) { out.push(m); continue; }
        let d = pollard_brent(&m, &mut budget)?;
        stack.push(&m / &d);
        stack.push(d);
    }
    out.sort();
    Some(out)
}

/// Every divisor of `n` from its prime factorisation.
fn divisors(primes: &[BigUint]) -> Vec<BigUint> {
    let mut divs = vec![BigUint::one()];
    let mut i = 0;
    while i < primes.len() {
        let p = &primes[i];
        let mut k = 0;
        while i + k < primes.len() && primes[i + k] == *p { k += 1; }
        let mut next = Vec::new();
        for d in &divs {
            let mut pw = BigUint::one();
            for _ in 0..=k { next.push(d * &pw); pw *= p; }
        }
        divs = next;
        i += k;
    }
    divs.sort(); divs.dedup();
    divs
}

// ─── the recogniser: structure first, conventions last ──────────────────────

/// What the structure pass finds: factor bits by relative weight, the product
/// columns by relative weight with their pinned output variables, and the
/// pinned variables belonging to no column.
struct Structure {
    a: Vec<i32>,
    b: Vec<i32>,
    /// per factor bit, whether the arithmetic bit is the negation of the variable
    /// (read off the partial-product AND gates: a shuffled instance flips every
    /// variable's polarity independently)
    qa: Vec<bool>,
    qb: Vec<bool>,
    /// per relative column weight, the pinned variables in that column
    /// (the sum output; at the top also the carry-out)
    cols: Vec<Vec<i32>>,
}

/// XOR relations: a set of k = 3 or 4 variables carrying all 2^(k−1) clauses
/// of one parity.  Such a relation joins variables of equal weight in any
/// adder network (a sum cell's inputs and output share a column).
fn parity_relations(clauses: &[Vec<i32>]) -> Vec<(Vec<u32>, bool)> {
    let mut by_set: std::collections::HashMap<Vec<u32>, Vec<usize>> = std::collections::HashMap::new();
    for (i, c) in clauses.iter().enumerate() {
        if c.len() == 3 || c.len() == 4 {
            let mut vs: Vec<u32> = c.iter().map(|l| l.unsigned_abs()).collect();
            vs.sort_unstable(); vs.dedup();
            if vs.len() == c.len() { by_set.entry(vs).or_default().push(i); }
        }
    }
    let mut rels = Vec::new();
    for (vs, idx) in by_set {
        let k = vs.len();
        if idx.len() != 1 << (k - 1) { continue; }
        let mut pats: Vec<u32> = idx.iter().map(|&i| clauses[i].iter().map(|&l| (l < 0) as u32).sum::<u32>() % 2).collect();
        pats.sort_unstable(); pats.dedup();
        if pats.len() == 1 { rels.push((vs, pats[0] == 1)); }   // a clause forbids the assignment making all its literals false: #true = #negative
    }
    rels
}

fn recognise_structure(nvars: usize, clauses: &[Vec<i32>]) -> Result<Structure, String> {
    let dbg = std::env::var("FACTORING_DEBUG").is_ok();
    let t0 = std::time::Instant::now();
    let phase = |what: &str| { if dbg { eprintln!("dbg structure: {what} at {:.1}ms", t0.elapsed().as_secs_f64() * 1000.0); } };
    let deadline = t0 + budget();
    let over = |what: &str| -> Result<(), String> { if std::time::Instant::now() > deadline { Err(format!("budget exhausted {what}")) } else { Ok(()) } };
    let pins: Vec<i32> = clauses.iter().filter(|c| c.len() == 1).map(|c| c[0]).collect();
    // a pinned product has at least a byte of output bits
    if pins.len() < 8 { return Err(format!("{} pinned variables", pins.len())); }
    let pinned: std::collections::HashSet<u32> = pins.iter().map(|l| l.unsigned_abs()).collect();
    let rels_q = parity_relations(clauses);
    if rels_q.len() < 4 { return Err(format!("{} parity relations", rels_q.len())); }
    let rels: Vec<Vec<u32>> = rels_q.into_iter().map(|(r, _)| r).collect();
    phase(&format!("{} parity relations, {} pins", rels.len(), pins.len()));
    over("after the parity relations")?;
    let mut in_rel = vec![false; nvars + 1];
    for r in &rels { for &v in r { in_rel[v as usize] = true; } }
    // columns: union-find over the unpinned members of each relation
    let mut parent: Vec<u32> = (0..=nvars as u32).collect();
    fn find(p: &mut [u32], mut x: u32) -> u32 { while p[x as usize] != x { p[x as usize] = p[p[x as usize] as usize]; x = p[x as usize]; } x }
    for r in &rels {
        let core: Vec<u32> = r.iter().copied().filter(|v| !pinned.contains(v)).collect();
        for w in core.windows(2) { let (a, b) = (find(&mut parent, w[0]), find(&mut parent, w[1])); if a != b { parent[a as usize] = b; } }
    }
    let mut col_of: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
    let mut ncols = 0usize;
    let mut roots: std::collections::HashMap<u32, usize> = std::collections::HashMap::new();
    for r in &rels { for &v in r { if !pinned.contains(&v) {
        let root = find(&mut parent, v);
        let id = *roots.entry(root).or_insert_with(|| { ncols += 1; ncols - 1 });
        col_of.insert(v, id);
    } } }
    // the factor bits: unpinned, in no relation, busy
    let mut occ = vec![0usize; nvars + 1];
    for c in clauses { for &l in c { occ[l.unsigned_abs() as usize] += 1; } }
    let mut inputs: Vec<i32> = (1..=nvars as i32).filter(|&v| !pinned.contains(&(v as u32)) && !in_rel[v as usize] && occ[v as usize] >= 4).collect();
    // Plausibility bounds before anything superlinear: a multiplier of a
    // few hundred bits per factor has a few hundred candidate bits, about
    // n_a·n_b sum cells, and pins for its product bits plus a few
    // constants — a verification circuit with thousands of units or
    // hundreds of thousands of candidates is rejected here in linear time.
    if inputs.len() < 4 { return Err(format!("{} candidate factor bits", inputs.len())); }
    if inputs.len() > 4096 { return Err(format!("{} candidate factor bits, more than any multiplier", inputs.len())); }
    if rels.len() > 4 * inputs.len() * inputs.len() + 64 { return Err(format!("{} parity relations for {} candidate bits", rels.len(), inputs.len())); }
    if pins.len() > 4 * inputs.len() + 64 { return Err(format!("{} pins for {} candidate bits", pins.len(), inputs.len())); }
    // … and among those, the ones meeting at least four other candidates in
    // gate clauses: a factor bit meets every bit of the other factor in its
    // partial-product gates, a gate output only its few inputs (4-core,
    // peeled incrementally on a co-occurrence graph built once)
    {
        let idx: std::collections::HashMap<i32, usize> = inputs.iter().enumerate().map(|(i, &v)| (v, i)).collect();
        let mut nb: Vec<std::collections::HashSet<usize>> = vec![std::collections::HashSet::new(); inputs.len()];
        for c in clauses.iter().filter(|c| c.len() <= 3) {
            let ins: Vec<usize> = c.iter().filter_map(|l| idx.get(&l.abs()).copied()).collect();
            for &x in &ins { for &y in &ins { if x != y { nb[x].insert(y); } } }
        }
        let mut alive = vec![true; inputs.len()];
        let mut deg: Vec<usize> = nb.iter().map(|s| s.len()).collect();
        let mut stack: Vec<usize> = (0..inputs.len()).filter(|&i| deg[i] < 4).collect();
        while let Some(i) = stack.pop() {
            if !alive[i] { continue; }
            alive[i] = false;
            for &j in &nb[i] { if alive[j] { deg[j] -= 1; if deg[j] < 4 { stack.push(j); } } }
        }
        inputs = inputs.iter().enumerate().filter(|(i, _)| alive[*i]).map(|(_, &v)| v).collect();
    }
    if inputs.len() < 4 { return Err(format!("{} candidate factor bits", inputs.len())); }
    over("after the candidate filter")?;
    phase(&format!("{} candidate factor bits after the 4-core", inputs.len()));
    let is_input = |v: i32| inputs.binary_search(&v).is_ok();
    // co-occurrence: bits of different factors meet in a gate clause (their partial
    // product), same-factor bits never do — longer clauses are side constraints
    // (toughsat's "the factor is not 1" clause names every bit of one factor)
    let mut co: std::collections::HashMap<i32, std::collections::HashSet<i32>> = std::collections::HashMap::new();
    for c in clauses.iter().filter(|c| c.len() <= 3) {
        let ins: Vec<i32> = c.iter().map(|l| l.unsigned_abs() as i32).filter(|&v| is_input(v)).collect();
        for &x in &ins { for &y in &ins { if x != y { co.entry(x).or_default().insert(y); } } }
    }
    let mut side: std::collections::HashMap<i32, u8> = std::collections::HashMap::new();
    side.insert(inputs[0], 0);
    let mut stack = vec![inputs[0]];
    while let Some(x) = stack.pop() {
        let sx = side[&x];
        for &y in co.get(&x).map(|s| s.iter().collect::<Vec<_>>()).unwrap_or_default() {
            if let std::collections::hash_map::Entry::Vacant(e) = side.entry(y) { e.insert(1 - sx); stack.push(y); } else if side[&y] == sx { return Err("factor-bit co-occurrence is not bipartite".into()); }
        }
    }
    if side.len() != inputs.len() { return Err("factor bits do not form one bipartite component".into()); }
    let a_bits: Vec<i32> = inputs.iter().copied().filter(|v| side[v] == 0).collect();
    let b_bits: Vec<i32> = inputs.iter().copied().filter(|v| side[v] == 1).collect();
    phase(&format!("bipartite {}x{}", a_bits.len(), b_bits.len()));
    over("after the bipartite split")?;
    // the column of each cross pair: the column of the other variables in a clause holding both
    let mut col_pair: std::collections::HashMap<(i32, i32), usize> = std::collections::HashMap::new();
    for c in clauses {
        let vs: Vec<i32> = c.iter().map(|l| l.unsigned_abs() as i32).collect();
        let xs: Vec<i32> = vs.iter().copied().filter(|&v| is_input(v) && side[&v] == 0).collect();
        let ys: Vec<i32> = vs.iter().copied().filter(|&v| is_input(v) && side[&v] == 1).collect();
        if xs.len() != 1 || ys.len() != 1 { continue; }
        let cols: Vec<usize> = vs.iter().filter_map(|&v| col_of.get(&(v as u32)).copied()).collect();
        if let Some(&cid) = cols.first()
            && cols.iter().all(|&c| c == cid) { col_pair.entry((xs[0], ys[0])).or_insert(cid); }
    }
    // the addition table: level sets are the columns; label from an end by induction
    let pairs_in = |cid: usize| -> Vec<(i32, i32)> { col_pair.iter().filter(|(_, c)| **c == cid).map(|(p, _)| *p).collect() };
    let used: std::collections::HashSet<usize> = col_pair.values().copied().collect();
    let ends: Vec<usize> = used.iter().copied().filter(|&c| pairs_in(c).len() == 1).collect();
    if ends.is_empty() || ends.len() > 2 { return Err(format!("{} single-pair columns (of {} columns touched by pairs, {} bits)", ends.len(), used.len(), inputs.len())); }
    let end = *ends.iter().min().unwrap();
    let (a0, b0) = pairs_in(end)[0];
    let mut wa: std::collections::HashMap<i32, usize> = std::collections::HashMap::new();
    let mut wb: std::collections::HashMap<i32, usize> = std::collections::HashMap::new();
    let mut wcol: std::collections::HashMap<usize, usize> = std::collections::HashMap::new();
    wa.insert(a0, 0); wb.insert(b0, 0); wcol.insert(end, 0);
    let total = a_bits.len() + b_bits.len() - 1;
    for m in 1..total {
        let mut found = None;
        for &cid in &used {
            if wcol.contains_key(&cid) { continue; }
            let ps = pairs_in(cid);
            let hit = if m == 1 { ps.len() == 2 && ps.iter().any(|&(x, _)| x == a0) && ps.iter().any(|&(_, y)| y == b0) }
                      else { ps.iter().any(|&(x, y)| matches!((wa.get(&x), wb.get(&y)), (Some(&i), Some(&j)) if i + j == m)) };
            if hit { found = Some(cid); break; }
        }
        let Some(cid) = found else {
            // the far end may have no sum cell (the lowest product bit is a bare partial
            // product, or implicit); by then every factor bit is labelled
            if wa.len() == a_bits.len() && wb.len() == b_bits.len() { break; }
            return Err(format!("no column of weight {m} with factor bits still unlabelled"));
        };
        wcol.insert(cid, m);
        for (x, y) in pairs_in(cid) {
            match (wa.get(&x).copied(), wb.get(&y).copied()) {
                (Some(i), None) => { wb.insert(y, m - i); }
                (None, Some(j)) => { wa.insert(x, m - j); }
                (Some(i), Some(j)) => { if i + j != m { return Err("inconsistent addition table".into()); } }
                (None, None) => return Err("a pair with no labelled end".into()),
            }
        }
    }
    if wa.len() != a_bits.len() || wb.len() != b_bits.len() { return Err("some factor bit has no weight".into()); }
    phase("addition table labelled");
    let mut a: Vec<(usize, i32)> = wa.iter().map(|(&v, &w)| (w, v)).collect(); a.sort();
    let mut b: Vec<(usize, i32)> = wb.iter().map(|(&v, &w)| (w, v)).collect(); b.sort();
    if a.iter().enumerate().any(|(i, &(w, _))| w != i) || b.iter().enumerate().any(|(j, &(w, _))| w != j) { return Err("factor weights are not 0..n−1".into()); }
    // pinned outputs per column: a pinned variable whose relation mates sit in the
    // column — unless it sits in relations of several columns (a pinned constant
    // the cells share, not a product bit)
    let mut pin_cols: std::collections::HashMap<i32, std::collections::HashSet<usize>> = std::collections::HashMap::new();
    for r in &rels {
        let mates: Vec<usize> = r.iter().filter_map(|v| col_of.get(v).copied()).collect();
        let Some(&cid) = mates.first() else { continue };
        let Some(&w) = wcol.get(&cid) else { continue };
        for &v in r { if pinned.contains(&v) { pin_cols.entry(v as i32).or_default().insert(w); } }
    }
    let mut cols: Vec<Vec<i32>> = vec![Vec::new(); total];
    for (v, ws) in &pin_cols { if ws.len() == 1 { cols[*ws.iter().next().unwrap()].push(*v); } }
    for c in &mut cols { c.sort_unstable(); }
    // the polarity of each factor bit from its partial-product gates: a 3-variable
    // gate over (x, y, p) with four clauses whose output table is an AND up to
    // polarities; the one input combination with the odd output value is where
    // both arithmetic bits are 1
    #[allow(clippy::type_complexity)]
    let mut gate: std::collections::HashMap<(i32, i32, i32), Vec<(bool, bool, bool)>> = std::collections::HashMap::new();   // forbidden (x, y, p) values
    for c in clauses {
        if c.len() != 3 { continue; }
        let xs: Vec<i32> = c.iter().filter(|l| is_input(l.abs()) && side[&l.abs()] == 0).copied().collect();
        let ys: Vec<i32> = c.iter().filter(|l| is_input(l.abs()) && side[&l.abs()] == 1).copied().collect();
        let ps: Vec<i32> = c.iter().filter(|l| !is_input(l.abs())).copied().collect();
        if xs.len() != 1 || ys.len() != 1 || ps.len() != 1 { continue; }
        gate.entry((xs[0].abs(), ys[0].abs(), ps[0].abs())).or_default().push((xs[0] < 0, ys[0] < 0, ps[0] < 0));
    }
    let binaries: std::collections::HashSet<(i32, i32)> = clauses.iter().filter(|c| c.len() == 2).map(|c| (c[0].min(c[1]), c[0].max(c[1]))).collect();
    let mut vote_a: std::collections::HashMap<i32, (usize, usize)> = std::collections::HashMap::new();
    let mut vote_b: std::collections::HashMap<i32, (usize, usize)> = std::collections::HashMap::new();
    for ((x, y, p), rows) in &gate {
        // the (x, y) combination where both arithmetic bits are 1: in a four-row
        // table the row whose output differs from the other three; in the minimal
        // encoding the single ternary clause, backed by its two binary clauses
        let odd: (bool, bool) = if rows.len() == 4 {
            let mut table: Vec<Option<bool>> = vec![None; 4];   // allowed p per (x, y) value
            for &(fx, fy, fp) in rows { table[(fx as usize) * 2 + fy as usize] = Some(!fp); }
            if table.iter().any(|t| t.is_none()) { continue; }
            let t: Vec<bool> = table.into_iter().map(|t| t.unwrap()).collect();
            let ones = t.iter().filter(|&&v| v).count();
            if ones != 1 && ones != 3 { continue; }   // not an AND up to polarities
            let k = (0..4).find(|&k| t[k] == (ones == 1)).unwrap();
            (k & 2 != 0, k & 1 != 0)
        } else if rows.len() == 1 {
            let (fx, fy, fp) = rows[0];
            let lit = |v: i32, f: bool| if f { v } else { -v };
            let (lx, ly, lp) = (lit(*x, fx), lit(*y, fy), lit(*p, fp));
            if !binaries.contains(&(lx.min(lp), lx.max(lp))) || !binaries.contains(&(ly.min(lp), ly.max(lp))) { continue; }
            (fx, fy)
        } else { continue };
        let (ax, by) = odd;
        let ea = vote_a.entry(*x).or_default(); if ax { ea.0 += 1 } else { ea.1 += 1 }
        let eb = vote_b.entry(*y).or_default(); if by { eb.0 += 1 } else { eb.1 += 1 }
    }
    let polarity = |votes: &std::collections::HashMap<i32, (usize, usize)>, v: i32| -> Result<bool, String> {
        match votes.get(&v) {
            Some(&(t, f)) if t > 0 && f == 0 => Ok(false),
            Some(&(t, f)) if f > 0 && t == 0 => Ok(true),
            Some(&(t, f)) => Err(format!("factor bit {v} is used with both polarities ({t} vs {f} gates)")),
            None => Err(format!("factor bit {v} has no AND-shaped partial-product gate")),
        }
    };
    let mut qa = Vec::new(); for &(_, v) in &a { qa.push(polarity(&vote_a, v)?); }
    let mut qb = Vec::new(); for &(_, v) in &b { qb.push(polarity(&vote_b, v)?); }
    Ok(Structure { a: a.into_iter().map(|(_, v)| v).collect(), b: b.into_iter().map(|(_, v)| v).collect(), qa, qb, cols })
}

/// The stage's wall-clock budget: `FACTORING_BUDGET_MS` (default 1000).
/// A multiplier of competition size is read in well under 200 ms; the
/// budget is the backstop for circuits that pass the cheap plausibility
/// bounds and still are not multipliers.
fn budget() -> std::time::Duration {
    let ms = std::env::var("FACTORING_BUDGET_MS").ok().and_then(|v| v.parse::<u64>().ok()).unwrap_or(1000);
    std::time::Duration::from_millis(ms)
}

/// Deterministic xorshift for the probes.
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 { let mut x = self.0; x ^= x << 13; x ^= x >> 7; x ^= x << 17; self.0 = x; x }
    fn bit(&mut self) -> bool { (self.next() >> 32) & 1 == 1 }
}

/// Assign the kept constants and a raw factor assignment and propagate.
/// Returns the number of falsified clauses (lenient mode evaluates the whole
/// circuit regardless; strict mode stops at the first, reported as 1).
fn probe(bcp: &mut Bcp, keep: &[i32], a: &[i32], b: &[i32], ra: &[bool], rb: &[bool]) -> usize {
    bcp.reset();
    let lits = keep.iter().copied()
        .chain(a.iter().enumerate().map(|(i, &v)| if ra[i] { v } else { -v }))
        .chain(b.iter().enumerate().map(|(j, &v)| if rb[j] { v } else { -v }));
    for l in lits { if !bcp.assign(l) && !bcp.lenient { return 1; } }
    bcp.conflicts
}

/// The value of a factor under a reading of its raw bits: bit `i` of the
/// oriented vector, flipped when `pol`, shifted up by one with a constant 1
/// below when `implicit` (an odd factor with its low bit left out).
fn factor_value(raw: &[bool], pol: &[bool], implicit: bool) -> BigUint {
    let mut x = BigUint::zero();
    for (i, &r) in raw.iter().enumerate() { if r != pol[i] { x += BigUint::one() << (i + implicit as usize); } }
    if implicit { x += BigUint::one(); }
    x
}

/// Run the tactic on a CNF.  `rho_budget` bounds Pollard–Brent's iterations.
///
/// After the structure pass the conventions are read off the circuit itself:
/// random factor assignments are propagated through the pin-free CNF, pinned
/// variables the factor bits never determine are the circuit's constants (kept
/// as pinned), and every other pin is matched against the bits of the product
/// under each reading of the factor bits (orientation, polarity, implicit odd
/// bit).  A reading that explains every pin over all probes fixes N.
pub fn factoring_tactic(nvars: usize, clauses: &[Vec<i32>], rho_budget: u64) -> Tactic {
    let t0 = std::time::Instant::now();
    let dbg = std::env::var("FACTORING_DEBUG").is_ok();
    let st = match recognise_structure(nvars, clauses) { Ok(s) => s, Err(e) => return Tactic::NotRecognised(e) };
    let pins: Vec<i32> = clauses.iter().filter(|c| c.len() == 1).map(|c| c[0]).collect();
    let (na, nb) = (st.a.len(), st.b.len());
    eprintln!("c factoring: structure {}×{}-bit factors over {} product columns, {} pinned variables, in {:.1}ms", na, nb, st.cols.len(), pins.len(), t0.elapsed().as_secs_f64() * 1000.0);
    let mut occ = vec![0usize; nvars + 1];
    for c in clauses { for &l in c { occ[l.unsigned_abs() as usize] += 1; } }
    let relevant: Vec<bool> = (1..=nvars).map(|v| occ[v] > 0).collect();
    let mut bcp = Bcp::new(nvars, clauses);
    // the probes: random raw factor bits
    const P: usize = 48;
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let ra: Vec<Vec<bool>> = (0..P).map(|_| (0..na).map(|_| rng.bit()).collect()).collect();
    let rb: Vec<Vec<bool>> = (0..P).map(|_| (0..nb).map(|_| rng.bit()).collect()).collect();
    // what a probe observes: a pinned variable's value, or whether a clause
    // group (the clauses over one variable set) is violated — a gate whose
    // output was folded into a constant at generation time (toughsat
    // substitutes the product bits into the last cells) is violated exactly
    // when the bit disagrees with the constant
    enum Obs { Pin(i32), Violated(Vec<u32>) }
    let npins = pins.len();
    let mut obs: Vec<Obs> = pins.iter().map(|&l| Obs::Pin(l)).collect();
    let violated_groups = |bcp: &Bcp| -> std::collections::HashSet<Vec<u32>> {
        let mut out = std::collections::HashSet::new();
        for c in clauses.iter().filter(|c| c.len() >= 2) {
            if c.iter().all(|&l| bcp.lit_val(l) == Some(false)) {
                let mut vs: Vec<u32> = c.iter().map(|l| l.unsigned_abs()).collect();
                vs.sort_unstable();
                out.insert(vs);
            }
        }
        out
    };
    // constants: pins the factor bits never determine, consistent with every probe
    bcp.lenient = true;
    let mut keep: Vec<i32> = Vec::new();
    let mut kept = vec![false; npins];
    let mut vals: Vec<Vec<Option<bool>>> = vec![vec![None; npins]; P];
    let mut base_conf = vec![0usize; P];   // falsified clauses per probe: folded cells disagreeing with N
    let mut violated: Vec<std::collections::HashSet<Vec<u32>>> = vec![std::collections::HashSet::new(); P];
    let deadline = t0 + budget();
    let over = |what: &str| -> Option<Tactic> { if std::time::Instant::now() > deadline { Some(Tactic::NotRecognised(format!("budget exhausted {what}"))) } else { None } };
    loop {
        for p in 0..P {
            if let Some(t) = over("while probing") { return t; }
            base_conf[p] = probe(&mut bcp, &keep, &st.a, &st.b, &ra[p], &rb[p]);
            for (k, &l) in pins.iter().enumerate() { vals[p][k] = bcp.lit_val(l); }
            violated[p] = violated_groups(&bcp);
        }
        let mut open: Vec<usize> = (0..npins).filter(|&k| !kept[k] && vals.iter().any(|v| v[k].is_none())).collect();
        if open.is_empty() { break; }
        open.sort_by_key(|&k| std::cmp::Reverse(occ[pins[k].unsigned_abs() as usize]));
        let mut progress = false;
        for k in open {
            if let Some(t) = over("while classifying constants") { return t; }
            // a constant adds no falsified clause to any probe
            keep.push(pins[k]);
            if (0..P).all(|p| probe(&mut bcp, &keep, &st.a, &st.b, &ra[p], &rb[p]) == base_conf[p]) { kept[k] = true; progress = true; } else { keep.pop(); }
        }
        if !progress {
            let n = (0..npins).filter(|&k| !kept[k] && vals.iter().any(|v| v[k].is_none())).count();
            return Tactic::NotRecognised(format!("{n} pinned variables are not determined by the factor bits"));
        }
    }
    // the outputs: every pin the probes vary (a pin the factor bits determine
    // but never vary is a side constraint — pyhala-braun pins "the factor is
    // not 1" — checked with the model, not read as a product bit), and every
    // clause group some probe violates
    let varies: Vec<bool> = (0..npins).map(|k| vals.iter().any(|v| v[k] != vals[0][k])).collect();
    let nside = (0..npins).filter(|&k| !kept[k] && !varies[k]).count();
    let mut groups: Vec<Vec<u32>> = violated.iter().flat_map(|s| s.iter().cloned()).collect::<std::collections::HashSet<_>>().into_iter().collect();
    groups.sort();
    for g in &groups {
        let k = obs.len();
        obs.push(Obs::Violated(g.clone()));
        for p in 0..P { vals[p].push(Some(violated[p].contains(&obs_group(&obs[k])))); }
    }
    fn obs_group(o: &Obs) -> Vec<u32> { match o { Obs::Violated(g) => g.clone(), Obs::Pin(_) => Vec::new() } }
    if dbg { eprintln!("dbg tactic: constants classified at {:.1}ms", t0.elapsed().as_secs_f64() * 1000.0); }
    let outputs: Vec<usize> = (0..obs.len()).filter(|&k| match &obs[k] { Obs::Pin(_) => !kept[k] && varies[k], Obs::Violated(_) => true }).collect();
    let nfold = groups.len();
    if dbg { eprintln!("dbg {} constants kept {:?}, {} side pins, {} outputs ({} violated clause groups)", keep.len(), keep, nside, outputs.len(), nfold); }
    if outputs.is_empty() { return Tactic::NotRecognised("no output pins".into()); }
    // readings of the factor bits.  An output that matches a product bit over
    // all probes (a chance match is a 2^-47 event) reads that bit of N; one
    // that matches nothing is a side constraint or a partial indicator (one
    // clause of a folded carry) and is left to the model check.  A reading
    // is accepted when at most a few bits of N are left unread.
    struct Reading { orientation: bool, ia: bool, ib: bool }
    #[allow(clippy::type_complexity)]
    let mut candidates: Vec<(BigUint, Reading, Vec<(usize, i32)>, usize)> = Vec::new();   // N, reading, (weight, pin) of the matched pins, unread bits
    for orientation in [false, true] { for ia in [false, true] { for ib in [false, true] {
        let oriented = |raw: &[bool]| -> Vec<bool> { if orientation { raw.iter().rev().copied().collect() } else { raw.to_vec() } };
        let (qa, qb) = (oriented(&st.qa), oriented(&st.qb));
        let prod: Vec<BigUint> = (0..P).map(|p| factor_value(&oriented(&ra[p]), &qa, ia) * factor_value(&oriented(&rb[p]), &qb, ib)).collect();
        let kmax = na + ia as usize + nb + ib as usize;   // the product is below 2^kmax
        let mut matched: Vec<(usize, i32)> = Vec::new();   // weight, pinned variable
        let mut nbits: Vec<Option<bool>> = vec![None; kmax];
        let (mut unexplained, mut inconsistent) = (0usize, 0usize);
        for &k in &outputs {
            let g: Vec<bool> = (0..P).map(|p| vals[p][k].unwrap()).collect();
            let mut hits: Vec<(usize, bool)> = Vec::new();
            for w in 0..kmax {
                let pol = g[0] != prod[0].bit(w as u64);
                if (1..P).all(|p| g[p] == (prod[p].bit(w as u64) != pol)) { hits.push((w, pol)); }
            }
            if hits.len() != 1 { unexplained += 1; continue; }
            let (w, pol) = hits[0];
            // a pinned literal is true in the solution: its bit is ¬pol; a folded
            // gate is violated exactly when the bit differs from N's: its bit is pol
            let bit = match &obs[k] { Obs::Pin(l) => { matched.push((w, *l)); !pol } Obs::Violated(_) => pol };
            if let Some(prev) = nbits[w] && prev != bit { inconsistent += 1; continue; }
            nbits[w] = Some(bit);
        }
        let missing: Vec<usize> = (0..kmax).filter(|&w| nbits[w].is_none()).collect();
        if dbg { eprintln!("dbg reading orient={orientation} implicit=({ia},{ib}): {} of {} outputs read a bit, {} unexplained, {} inconsistent, unread weights {:?}", outputs.len() - unexplained - inconsistent, outputs.len(), unexplained, inconsistent, missing); }
        if inconsistent > 0 || missing.len() > 6 { continue; }
        matched.sort();
        let mut base = BigUint::zero();
        for (w, v) in nbits.iter().enumerate() { if *v == Some(true) { base += BigUint::one() << w; } }
        for fill in 0..(1u64 << missing.len()) {
            let mut n = base.clone();
            for (t, &w) in missing.iter().enumerate() { if fill >> t & 1 == 1 { n += BigUint::one() << w; } }
            if n.is_zero() { continue; }
            if (ia || ib) && n.is_even() { continue; }
            candidates.push((n, Reading { orientation, ia, ib }, matched.clone(), missing.len()));
        }
    } } }
    candidates.sort_by_key(|c| c.3);
    bcp.lenient = false;
    if candidates.is_empty() { return Tactic::NotRecognised(format!("no reading of the factor bits explains the {} outputs ({} pins, {} violated clause groups)", outputs.len(), outputs.len() - nfold, nfold)); }
    eprintln!("c factoring: {} candidate numbers from {} readings ({} constants, {} side pins, {} folded gates) in {:.1}ms", candidates.len(), candidates.iter().map(|c| (c.1.orientation, c.1.ia, c.1.ib)).collect::<std::collections::HashSet<_>>().len(), keep.len(), nside, nfold, t0.elapsed().as_secs_f64() * 1000.0);
    let mut tried = 0usize;
    let mut first_info: Option<Multiplier> = None;
    for (n, rd, matched, _) in &candidates {
        if let Some(t) = over("while factoring") { return t; }
        let (a, b): (Vec<i32>, Vec<i32>) = if rd.orientation { (st.a.iter().rev().copied().collect(), st.b.iter().rev().copied().collect()) } else { (st.a.clone(), st.b.clone()) };
        let (qa, qb): (Vec<bool>, Vec<bool>) = if rd.orientation { (st.qa.iter().rev().copied().collect(), st.qb.iter().rev().copied().collect()) } else { (st.qa.clone(), st.qb.clone()) };
        let info = Multiplier { a: a.clone(), b: b.clone(), out: matched.iter().map(|&(_, v)| v).collect(), n: n.clone() };
        if first_info.is_none() { first_info = Some(info.clone()); }
        let Some(primes) = factorize(n, rho_budget) else { eprintln!("c factoring: N = {n}: factoring budget exhausted"); continue };
        if dbg { eprintln!("dbg N={n} primes={:?}", primes); }
        let divs = divisors(&primes);
        let lim_a = BigUint::one() << (na + rd.ia as usize);
        let lim_b = BigUint::one() << (nb + rd.ib as usize);
        for d in &divs {
            let e = n / d;
            for (fa, fb) in [(d, &e), (&e, d)] {
                if *fa >= lim_a || *fb >= lim_b { continue; }
                if (rd.ia && fa.is_even()) || (rd.ib && fb.is_even()) { continue; }
                tried += 1;
                bcp.reset();
                let mut good = true;
                for &p in &pins { if !bcp.assign(p) { good = false; break; } }
                let (xa, xb) = ((fa - BigUint::from(rd.ia as u8)) >> (rd.ia as usize), (fb - BigUint::from(rd.ib as u8)) >> (rd.ib as usize));
                if good { for (i, &v) in a.iter().enumerate() { let set = xa.bit(i as u64) != qa[i]; if !bcp.assign(if set { v } else { -v }) { good = false; break; } } }
                if good { for (j, &v) in b.iter().enumerate() { let set = xb.bit(j as u64) != qb[j]; if !bcp.assign(if set { v } else { -v }) { good = false; break; } } }
                if good { for v in 1..=nvars as i32 { if relevant[v as usize - 1] && bcp.lit_val(v).is_none() && !bcp.assign(-v) { good = false; break; } } }
                if good {
                    let model = bcp.model();
                    if clauses.iter().all(|c| c.iter().any(|&l| model[l.unsigned_abs() as usize - 1] == (l > 0))) {
                        eprintln!("c factoring: N = {} = {} × {} — model by propagation in {:.1}ms ({} pairs tried{}{})", n, fa, fb, t0.elapsed().as_secs_f64() * 1000.0, tried,
                                  if rd.ia || rd.ib { ", odd factors" } else { "" }, if qa.iter().chain(&qb).any(|&q| q) { ", mixed polarities" } else { "" });
                        return Tactic::Sat { model, info };
                    }
                }
            }
        }
    }
    match first_info {
        Some(info) => { eprintln!("c factoring: no factor pair fits ({} candidate numbers, {} pairs tried, {:.1}ms)", candidates.len(), tried, t0.elapsed().as_secs_f64() * 1000.0); Tactic::NoFactorPair { info } }
        None => Tactic::NotRecognised("no readable product".into()),
    }
}

// ─── tests ──────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    /// A Tseitin array multiplier: partial products as AND gates, ripple
    /// rows of full adders (XOR3 + majority), outputs pinned to `n`.
    fn fresh(next: &mut i32) -> i32 { *next += 1; *next }
    #[allow(clippy::type_complexity)] // (nvars, clauses, p bits, q bits, product bits)
    fn tseitin_multiplier(bits: usize, n: u64, pin: bool) -> (usize, Vec<Vec<i32>>, Vec<i32>, Vec<i32>, Vec<i32>) {
        let mut next = 0i32;
        let a: Vec<i32> = (0..bits).map(|_| fresh(&mut next)).collect();
        let b: Vec<i32> = (0..bits).map(|_| fresh(&mut next)).collect();
        let mut cls: Vec<Vec<i32>> = Vec::new();
        // partial products
        let mut pp = vec![vec![0i32; bits]; bits];
        for i in 0..bits { for j in 0..bits {
            let p = fresh(&mut next); pp[i][j] = p;
            cls.push(vec![-a[i], -b[j], p]); cls.push(vec![a[i], -p]); cls.push(vec![b[j], -p]);
        } }
        fn fa(next: &mut i32, x: i32, y: i32, z: i32, cls: &mut Vec<Vec<i32>>) -> (i32, i32) {
            let s = fresh(next); let c = fresh(next);
            for m in 0..8u32 {   // s = x ⊕ y ⊕ z
                let (bx, by, bz) = (m & 1 != 0, m & 2 != 0, m & 4 != 0);
                let bs = bx ^ by ^ bz;
                // forbid the assignment (bx,by,bz,¬bs)
                cls.push(vec![if bx { -x } else { x }, if by { -y } else { y }, if bz { -z } else { z }, if bs { s } else { -s }]);
            }
            cls.push(vec![-x, -y, c]); cls.push(vec![-x, -z, c]); cls.push(vec![-y, -z, c]);
            cls.push(vec![x, y, -c]); cls.push(vec![x, z, -c]); cls.push(vec![y, z, -c]);
            (s, c)
        }
        // column sums with carries (schoolbook, ripple through columns)
        let mut cols: Vec<Vec<i32>> = vec![Vec::new(); 2 * bits];
        for i in 0..bits { for j in 0..bits { cols[i + j].push(pp[i][j]); } }
        let zero = fresh(&mut next); cls.push(vec![-zero]);
        let mut out = Vec::new();
        for w in 0..2 * bits {
            while cols[w].len() > 1 {
                let x = cols[w].pop().unwrap(); let y = cols[w].pop().unwrap();
                let z = if cols[w].is_empty() { zero } else { cols[w].pop().unwrap() };
                let (s, c) = fa(&mut next, x, y, z, &mut cls);
                cols[w].push(s);
                if w + 1 < 2 * bits { cols[w + 1].push(c); }
            }
            out.push(if cols[w].is_empty() { zero } else { cols[w][0] });
        }
        if pin { for (w, &o) in out.iter().enumerate() { if o != zero { cls.push(vec![if n >> w & 1 == 1 { o } else { -o }]); } else if n >> w & 1 == 1 { cls.push(vec![zero]); } } }
        (next as usize, cls, a, b, out)
    }

    #[test]
    fn recognises_a_tseitin_multiplier_and_factors() {
        let (nv, cls, a, b, _) = tseitin_multiplier(6, 35 * 41, true);   // 35·41 = 1435 < 2^12
        match factoring_tactic(nv, &cls, 1_000_000) {
            Tactic::Sat { model, info } => {
                assert_eq!(info.n, BigUint::from(1435u32));
                assert_eq!(info.a.len(), 6); assert_eq!(info.b.len(), 6);
                assert!(cls.iter().all(|c| c.iter().any(|&l| model[l.unsigned_abs() as usize - 1] == (l > 0))), "model violates a clause");
                let val = |bits: &[i32]| bits.iter().enumerate().map(|(i, &v)| (model[v as usize - 1] as u64) << i).sum::<u64>();
                let (x, y) = (val(&a), val(&b));
                assert_eq!(x * y, 1435, "{x} × {y}");
            }
            other => panic!("expected SAT, got {other:?}"),
        }
    }

    #[test]
    fn a_prime_has_no_pair() {
        let (nv, cls, _, _, _) = tseitin_multiplier(6, 3163, true);   // prime, needs 12 bits; factors 1 × 3163 do not fit 6 bits
        match factoring_tactic(nv, &cls, 1_000_000) {
            Tactic::NoFactorPair { info } => assert_eq!(info.n, BigUint::from(3163u32)),
            other => panic!("expected NoFactorPair, got {other:?}"),
        }
    }

    #[test]
    fn cook_detector_ignores_a_multiplier() {
        for n in [1435u64, 3163] {
            let (nv, cls, _, _, _) = tseitin_multiplier(6, n, true);
            assert!(matches!(crate::cook_pbp::detect_shape(&cls, nv), crate::cook_pbp::CnfShape::Unknown), "N = {n}");
        }
    }

    /// The residual of a multiplier after its pins are propagated away
    /// (what a unit-propagating preprocessor hands on) is satisfiable and
    /// must not be mistaken for a Cook refutation shape either.
    #[test]
    fn cook_detector_ignores_a_propagated_multiplier() {
        let (nv, cls, _, _, _) = tseitin_multiplier(6, 1435, true);
        let mut val: Vec<Option<bool>> = vec![None; nv];
        let mut queue: Vec<i32> = cls.iter().filter(|c| c.len() == 1).map(|c| c[0]).collect();
        while let Some(l) = queue.pop() {
            let v = l.unsigned_abs() as usize - 1;
            if val[v].is_some() { continue; }
            val[v] = Some(l > 0);
            for c in &cls {
                if c.iter().any(|&m| val[m.unsigned_abs() as usize - 1] == Some(m > 0)) { continue; }
                let open: Vec<i32> = c.iter().copied().filter(|&m| val[m.unsigned_abs() as usize - 1].is_none()).collect();
                if open.len() == 1 { queue.push(open[0]); }
            }
        }
        let residual: Vec<Vec<i32>> = cls.iter()
            .filter(|c| !c.iter().any(|&m| val[m.unsigned_abs() as usize - 1] == Some(m > 0)))
            .map(|c| c.iter().copied().filter(|&m| val[m.unsigned_abs() as usize - 1].is_none()).collect())
            .collect();
        let shape = crate::cook_pbp::detect_shape(&residual, nv);
        assert!(matches!(shape, crate::cook_pbp::CnfShape::Unknown), "residual ({} clauses) detected as {}", residual.len(), shape.describe());
    }

    #[test]
    fn factorize_small_numbers() {
        let f = factorize(&BigUint::from(1435u32), 1000).unwrap();
        assert_eq!(f, vec![BigUint::from(5u32), BigUint::from(7u32), BigUint::from(41u32)]);
        assert!(is_probable_prime(&BigUint::from(3163u32)));
        assert!(!is_probable_prime(&BigUint::from(1435u32)));
        let big = BigUint::parse_bytes(b"18446744073709551557", 10).unwrap();   // the largest 64-bit prime
        assert!(is_probable_prime(&big));
    }

    /// The real thing when the competition files are around (else skipped).
    #[test]
    fn ezfact_instances_if_present() {
        let dir = std::path::Path::new("/Users/greg/projects/sat_benchmarks");
        if !dir.exists() { return; }
        let mut seen = 0;
        for entry in std::fs::read_dir(dir).unwrap() {
            let p = entry.unwrap().path();
            let name = p.file_name().unwrap().to_string_lossy().to_string();
            if !(name.contains("ezfact16_") || name.contains("ezfact32_")) { continue; }
            let out = std::process::Command::new("xz").args(["-dc", p.to_str().unwrap()]).output().unwrap();
            let text = String::from_utf8(out.stdout).unwrap();
            let mut nv = 0usize; let mut cls = Vec::new();
            for line in text.lines() {
                if line.starts_with('c') { continue; }
                if line.starts_with('p') { nv = line.split_whitespace().nth(2).unwrap().parse().unwrap(); continue; }
                let c: Vec<i32> = line.split_whitespace().filter_map(|t| t.parse().ok()).take_while(|&l| l != 0).collect();
                if !c.is_empty() { cls.push(c); }
            }
            let r = factoring_tactic(nv, &cls, 5_000_000);
            match &r {
                Tactic::Sat { model, .. } => assert!(cls.iter().all(|c| c.iter().any(|&l| model[l.unsigned_abs() as usize - 1] == (l > 0))), "{name}: bad model"),
                Tactic::NoFactorPair { .. } => assert!(name.contains("ezfact16_"), "{name}: unexpected NoFactorPair"),
                Tactic::NotRecognised(why) => panic!("{name}: not recognised: {why}"),
            }
            seen += 1;
        }
        eprintln!("ezfact instances checked: {seen}");
    }
}
