//! lns48: value-set large-neighbourhood search for minimum-operation linear
//! programs over Z[1/2] -- a Rust port of the method of R. Patel's
//! `rebuild2.py` (rp440/matmul-4x4-48-202, CC0), with PLinOpt's cost model
//! (one operation per produced signal: additions and scalings; copies and
//! negations are free).
//!
//! A program for a linear map is identified with the SET of signal vectors
//! it computes; its cost is the number of non-input signals.  A set is
//! feasible when it is closed under one-gate productions: every signal is
//! u +- v, c u (c = 2, 1/2, or the ratio of two proportional signals) of
//! signals produced before it.  Each step proposes a few new signals from
//! six families (target residuals, coordinated residual packages, sparse
//! pivots, internal residuals, dyadic half/double pairs, broad random
//! combinations), adds them to the dictionary, reverse-deletes removable
//! signals in random order while the set stays closed, and accepts
//! descents, plateau moves (equal cost, not in the tabu list) and best+1
//! annealing moves.  Every emitted program is re-evaluated exactly against
//! the targets before it is written.
//!
//! Inputs are the 16 entries of a 4x4 matrix (L and R of a rank-r scheme,
//! or the transpose P^T of its output map); vectors are held as integer
//! numerators over SCAL = 64.
//!
//! Usage: lns48 --slp SEED.slp [--sms MATRIX.sms] --out DIR [--wall 60]
//!              [--seeds 4] [--seed 1] [--temperature 0.2] [--tabu 256]
//!              [--orders 4] [--log 30]
//!        lns48 --sms MATRIX.sms --out DIR ...     (naive chain seed)

use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::{BuildHasherDefault, Hasher};
use std::io::Write;
use std::num::NonZeroU32;
use std::time::{Duration, Instant};

#[cfg(not(feature = "n48"))]
const N: usize = 16; // inputs: the 16 entries of a 4x4 matrix (L, R, P^T)
#[cfg(feature = "n48")]
const N: usize = 48; // inputs: the 48 products (the output map P searched directly)
const SCAL: i64 = 64;
const MAXNUM: i64 = 16 * SCAL;
const MAXD: usize = 4096;
const NONE: u16 = u16::MAX;

type V = [i64; N];

// ------------------------------------------------------------------ hashing
#[derive(Default)]
struct FxHasher(u64);
impl Hasher for FxHasher {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, bytes: &[u8]) {
        for b in bytes {
            self.0 = (self.0.rotate_left(5) ^ (*b as u64)).wrapping_mul(0x517cc1b727220a95);
        }
    }
    fn write_i64(&mut self, i: i64) {
        self.0 = (self.0.rotate_left(5) ^ (i as u64)).wrapping_mul(0x517cc1b727220a95);
    }
    fn write_usize(&mut self, i: usize) {
        self.write_i64(i as i64);
    }
}
type FxMap<K, Vv> = HashMap<K, Vv, BuildHasherDefault<FxHasher>>;
type FxSet<K> = HashSet<K, BuildHasherDefault<FxHasher>>;

fn fingerprint(vals: &[V]) -> u64 {
    let mut sorted: Vec<V> = vals.to_vec();
    sorted.sort();
    let mut h = FxHasher(0x9e3779b97f4a7c15);
    for v in &sorted {
        for x in v {
            h.write_i64(*x);
        }
    }
    h.finish()
}

// ------------------------------------------------------------------ vectors
fn vadd(a: &V, b: &V) -> V {
    let mut r = [0; N];
    for i in 0..N {
        r[i] = a[i] + b[i];
    }
    r
}
fn vsub(a: &V, b: &V) -> V {
    let mut r = [0; N];
    for i in 0..N {
        r[i] = a[i] - b[i];
    }
    r
}
fn vscale(a: &V, num: i64, den: i64) -> Option<V> {
    let mut r = [0; N];
    for i in 0..N {
        let x = a[i] * num;
        if x % den != 0 {
            return None;
        }
        r[i] = x / den;
        if r[i].abs() > MAXNUM {
            return None;
        }
    }
    Some(r)
}
fn in_range(a: &V) -> bool {
    a.iter().all(|x| x.abs() <= MAXNUM)
}
fn is_zero(a: &V) -> bool {
    a.iter().all(|x| *x == 0)
}
fn nnz(a: &V) -> usize {
    a.iter().filter(|x| **x != 0).count()
}
/// canonical direction (first nonzero coordinate positive) and the sign that maps it back
fn canon(a: &V) -> (V, i64) {
    for x in a {
        if *x != 0 {
            if *x < 0 {
                let mut r = [0; N];
                for i in 0..N {
                    r[i] = -a[i];
                }
                return (r, -1);
            }
            return (*a, 1);
        }
    }
    (*a, 1)
}
fn unit(j: usize) -> V {
    let mut r = [0; N];
    r[j] = SCAL;
    r
}
fn gcd(a: i64, b: i64) -> i64 {
    let (mut a, mut b) = (a.abs(), b.abs());
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

// ------------------------------------------------------------------ bitsets
#[derive(Clone, Copy, PartialEq, Eq)]
struct Bits([u64; 64]);
impl Default for Bits {
    fn default() -> Self {
        Bits([0; 64])
    }
}
impl Bits {
    fn get(&self, i: usize) -> bool {
        self.0[i >> 6] >> (i & 63) & 1 == 1
    }
    fn set(&mut self, i: usize) {
        self.0[i >> 6] |= 1 << (i & 63);
    }
    fn clear(&mut self, i: usize) {
        self.0[i >> 6] &= !(1 << (i & 63));
    }
    fn subset_of(&self, o: &Bits) -> bool {
        (0..64).all(|k| self.0[k] & !o.0[k] == 0)
    }
    fn and(&self, o: &Bits) -> Bits {
        let mut r = *self;
        for k in 0..64 {
            r.0[k] &= o.0[k];
        }
        r
    }
    fn and_not(&self, o: &Bits) -> Bits {
        let mut r = *self;
        for k in 0..64 {
            r.0[k] &= !o.0[k];
        }
        r
    }
    fn or(&self, o: &Bits) -> Bits {
        let mut r = *self;
        for k in 0..64 {
            r.0[k] |= o.0[k];
        }
        r
    }
    fn any(&self) -> bool {
        self.0.iter().any(|w| *w != 0)
    }
    fn count(&self) -> usize {
        self.0.iter().map(|w| w.count_ones() as usize).sum()
    }
    fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        (0..64).flat_map(move |k| {
            let mut w = self.0[k];
            std::iter::from_fn(move || {
                if w == 0 {
                    None
                } else {
                    let b = w.trailing_zeros() as usize;
                    w &= w - 1;
                    Some(k * 64 + b)
                }
            })
        })
    }
    fn full(n: usize) -> Bits {
        let mut r = Bits::default();
        for i in 0..n {
            r.set(i);
        }
        r
    }
}

// ------------------------------------------------------------------ rng
struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn f64(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
    fn shuffle<T>(&mut self, v: &mut [T]) {
        for i in (1..v.len()).rev() {
            let j = self.below(i + 1);
            v.swap(i, j);
        }
    }
    fn choose<'a, T>(&mut self, v: &'a [T]) -> &'a T {
        &v[self.below(v.len())]
    }
    fn weighted(&mut self, w: &[f64]) -> usize {
        let total: f64 = w.iter().sum();
        let mut x = self.f64() * total;
        for (i, wi) in w.iter().enumerate() {
            if x < *wi {
                return i;
            }
            x -= wi;
        }
        w.len() - 1
    }
    fn sign(&mut self) -> i64 {
        if self.next() & 1 == 0 { 1 } else { -1 }
    }
}

// ------------------------------------------------------------------ productions
/// x = a u + b v (binary, a, b in +-1; v != NONE) or x = (num/den) u (scaling, v == NONE)
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
struct Prod {
    u: u16,
    v: u16,
    a: i8,
    b: i8,
    num: i32,
    den: i32,
}

/// a production with its operands as vectors (dictionary-independent), used as a witness
#[derive(Clone, Debug)]
struct ProdV {
    u: V,
    v: Option<V>,
    a: i64,
    b: i64,
    num: i64,
    den: i64,
}

struct Dict {
    vals: Vec<V>,
    index: FxMap<V, usize>,
}
impl Dict {
    fn new() -> Dict {
        let mut d = Dict { vals: Vec::new(), index: FxMap::default() };
        for j in 0..N {
            d.insert(&unit(j));
        }
        d
    }
    /// insert the direction of v; returns (index, sign with v = sign * direction)
    fn insert(&mut self, v: &V) -> (usize, i64) {
        let (c, s) = canon(v);
        if let Some(i) = self.index.get(&c) {
            return (*i, s);
        }
        let i = self.vals.len();
        self.vals.push(c);
        self.index.insert(c, i);
        (i, s)
    }
    fn get(&self, v: &V) -> Option<(usize, i64)> {
        let (c, s) = canon(v);
        self.index.get(&c).map(|i| (*i, s))
    }
}

struct Catalog {
    opts: Vec<Vec<Prod>>,
    deps: Vec<Vec<Bits>>,
    inputs: Bits,
    required: Bits,
    n: usize,
}

impl Catalog {
    fn build(dict: &Dict, targets: &Bits, witness: &FxMap<V, ProdV>) -> Option<Catalog> {
        let n = dict.vals.len();
        if n > MAXD {
            return None;
        }
        let mut opts: Vec<Vec<Prod>> = vec![Vec::new(); n];
        let vals = &dict.vals;
        // binary productions
        for i in 0..n {
            for j in (i + 1)..n {
                let s = vadd(&vals[i], &vals[j]);
                if in_range(&s) {
                    if let Some(&x) = dict.index.get(&canon(&s).0) {
                        if x >= N && x != i && x != j {
                            let sg = canon(&s).1 as i8; // x_dir = sg * (vi + vj)
                            opts[x].push(Prod { u: i as u16, v: j as u16, a: sg, b: sg, num: 0, den: 0 });
                        }
                    }
                }
                let d = vsub(&vals[i], &vals[j]);
                if !is_zero(&d) && in_range(&d) {
                    if let Some(&x) = dict.index.get(&canon(&d).0) {
                        if x >= N && x != i && x != j {
                            let sg = canon(&d).1 as i8; // x_dir = sg * (vi - vj)
                            opts[x].push(Prod { u: i as u16, v: j as u16, a: sg, b: -sg, num: 0, den: 0 });
                        }
                    }
                }
            }
        }
        // scalings: proportional groups (ratio of first nonzero coordinates)
        let mut groups: FxMap<V, Vec<usize>> = FxMap::default();
        for (i, v) in vals.iter().enumerate() {
            let f = v.iter().find(|x| **x != 0).copied().unwrap_or(0);
            if f == 0 {
                continue;
            }
            // key: v / f with denominator cleared by SCAL*SCAL (exact rational direction)
            let mut key = [0i64; N];
            let mut ok = true;
            for k in 0..N {
                let num = v[k] * SCAL * SCAL;
                if num % f != 0 {
                    ok = false;
                    break;
                }
                key[k] = num / f;
            }
            if ok {
                groups.entry(key).or_default().push(i);
            }
        }
        for g in groups.values() {
            if g.len() < 2 {
                continue;
            }
            for &x in g {
                if x < N {
                    continue;
                }
                for &u in g {
                    if u == x {
                        continue;
                    }
                    let fx = vals[x].iter().find(|t| **t != 0).copied().unwrap();
                    let fu = vals[u].iter().find(|t| **t != 0).copied().unwrap();
                    let gg = gcd(fx, fu);
                    let (num, den) = (fx / gg, fu / gg);
                    if num.abs() > 64 || den.abs() > 64 || den == 0 {
                        continue;
                    }
                    let (num, den) = if den < 0 { (-num, -den) } else { (num, den) };
                    if (num == 1 || num == -1) && den == 1 {
                        continue; // a copy, not a production of a new direction
                    }
                    opts[x].push(Prod { u: u as u16, v: NONE, a: 0, b: 0, num: num as i32, den: den as i32 });
                }
            }
        }
        // witness first
        for x in N..n {
            if let Some(w) = witness.get(&vals[x]) {
                let pos = opts[x].iter().position(|p| prod_matches(p, w, dict));
                if let Some(k) = pos {
                    if k > 0 {
                        let p = opts[x].remove(k);
                        opts[x].insert(0, p);
                    }
                }
            }
        }
        let deps = opts
            .iter()
            .map(|os| {
                os.iter()
                    .map(|p| {
                        let mut b = Bits::default();
                        b.set(p.u as usize);
                        if p.v != NONE {
                            b.set(p.v as usize);
                        }
                        b
                    })
                    .collect()
            })
            .collect();
        let inputs = Bits::full(N);
        Some(Catalog { opts, deps, inputs, required: inputs.or(targets), n })
    }

    /// greedy monotone closure over integer masks; returns the production order when it closes
    fn closure(&self, selected: &Bits, trace: Option<&mut Vec<(usize, usize)>>) -> bool {
        if !self.required.subset_of(selected) {
            return false;
        }
        let mut closed = self.inputs;
        let mut remaining = selected.and_not(&closed);
        let mut tr = trace;
        loop {
            let mut progress = false;
            for x in remaining.iter().collect::<Vec<_>>() {
                for (k, d) in self.deps[x].iter().enumerate() {
                    if d.subset_of(&closed) {
                        closed.set(x);
                        remaining.clear(x);
                        progress = true;
                        if let Some(t) = tr.as_deref_mut() {
                            t.push((x, k));
                        }
                        break;
                    }
                }
            }
            if !remaining.any() {
                return true;
            }
            if !progress {
                return false;
            }
        }
    }
}

fn prod_matches(p: &Prod, w: &ProdV, dict: &Dict) -> bool {
    let u = match dict.get(&w.u) {
        Some((i, _)) => i,
        None => return false,
    };
    match &w.v {
        None => p.v == NONE && p.u as usize == u,
        Some(vv) => match dict.get(vv) {
            Some((j, _)) => p.v != NONE && ((p.u as usize == u && p.v as usize == j) || (p.u as usize == j && p.v as usize == u)),
            None => false,
        },
    }
}

/// reverse deletion from the full set; returns the chosen set (Patel: with novel
/// proposals present, the cheapest state that still contains one of them)
fn reverse_delete(cat: &Catalog, rng: &mut Rng, reps: usize, novel: &Bits) -> Bits {
    let full = Bits::full(cat.n);
    let mut best: Option<(usize, Bits)> = None;
    let mut moved: Option<(usize, Bits)> = None;
    for _ in 0..reps {
        let mut selected = full;
        let keep = |sel: &Bits, best: &mut Option<(usize, Bits)>, moved: &mut Option<(usize, Bits)>| {
            let c = sel.count();
            if best.is_none() || c <= best.as_ref().unwrap().0 {
                *best = Some((c, *sel));
            }
            if sel.and(novel).any() && (moved.is_none() || c <= moved.as_ref().unwrap().0) {
                *moved = Some((c, *sel));
            }
        };
        keep(&selected, &mut best, &mut moved);
        loop {
            let mut changed = false;
            let mut removable: Vec<usize> = selected.and_not(&cat.required).iter().collect();
            rng.shuffle(&mut removable);
            for x in removable {
                let mut trial = selected;
                trial.clear(x);
                if cat.closure(&trial, None) {
                    selected = trial;
                    changed = true;
                    keep(&selected, &mut best, &mut moved);
                }
            }
            if !changed {
                break;
            }
        }
    }
    if novel.any() {
        if let Some((_, m)) = moved {
            return m;
        }
    }
    best.unwrap().1
}

/// exact repair: the minimum closed subset of the dictionary containing the
/// inputs and targets, as a MIP (HiGHS): x_v selects a vector, y_p a
/// production of v (both operands selected), sum_p y_p >= x_v, acyclicity by
/// continuous levels with a big-M on selected productions.  Returns the set
/// (verified closed) even when HiGHS stopped at the time limit.
fn mip_select(cat: &Catalog, time_limit: f64) -> Option<Bits> {
    mip_select_cap(cat, time_limit, None)
}

/// with `cap`: feasibility only -- sum of selected non-inputs <= cap (zero objective)
fn mip_select_cap(cat: &Catalog, time_limit: f64, cap: Option<usize>) -> Option<Bits> {
    let d = cat.n;
    let mut pb = highs::RowProblem::default();
    let x: Vec<highs::Col> = (0..d)
        .map(|v| {
            let fixed = v < N || cat.required.get(v);
            pb.add_integer_column(if v < N || cap.is_some() { 0.0 } else { 1.0 }, if fixed { 1.0..=1.0 } else { 0.0..=1.0 })
        })
        .collect();
    let mut prods: Vec<(usize, usize, Option<usize>)> = Vec::new();
    for v in N..d {
        for p in &cat.opts[v] {
            prods.push((v, p.u as usize, if p.v == NONE { None } else { Some(p.v as usize) }));
        }
    }
    let y: Vec<highs::Col> = prods.iter().map(|_| pb.add_integer_column(0.0, 0.0..=1.0)).collect();
    let lv: Vec<highs::Col> = (0..d).map(|v| pb.add_column(0.0, 0.0..=(if v < N { 0.0 } else { d as f64 }))).collect();
    let m = (d + 1) as f64;
    for (pi, &(v, u, w)) in prods.iter().enumerate() {
        pb.add_row(..=0.0, [(y[pi], 1.0), (x[u], -1.0)]);
        pb.add_row((1.0 - m).., [(lv[v], 1.0), (lv[u], -1.0), (y[pi], -m)]);
        if let Some(w) = w {
            pb.add_row(..=0.0, [(y[pi], 1.0), (x[w], -1.0)]);
            pb.add_row((1.0 - m).., [(lv[v], 1.0), (lv[w], -1.0), (y[pi], -m)]);
        }
    }
    let mut by_v: Vec<Vec<usize>> = vec![Vec::new(); d];
    for (pi, &(v, _, _)) in prods.iter().enumerate() {
        by_v[v].push(pi);
    }
    for v in N..d {
        let mut row: Vec<(highs::Col, f64)> = by_v[v].iter().map(|&pi| (y[pi], 1.0)).collect();
        row.push((x[v], -1.0));
        pb.add_row(0.0.., row);
    }
    if let Some(c) = cap {
        let row: Vec<(highs::Col, f64)> = (N..d).map(|v| (x[v], 1.0)).collect();
        pb.add_row(..=(c as f64), row);
    }
    let mut model = pb.optimise(highs::Sense::Minimise);
    model.make_quiet();
    model.set_threads(NonZeroU32::new(1).unwrap());
    model.set_option("time_limit", time_limit);
    let solved = model.solve();
    let status = solved.status();
    if cap.is_some() {
        eprintln!("  feasibility MIP (cap {}): status {:?}", cap.unwrap(), status);
    }
    let cols = solved.get_solution().columns().to_vec();
    if cols.len() < d {
        return None;
    }
    let mut sel = Bits::default();
    for v in 0..d {
        if cols[v] > 0.5 {
            sel.set(v);
        }
    }
    if cat.closure(&sel, None) { Some(sel) } else { None }
}

/// acyclicity encoding of the feasibility CNF
#[derive(Clone, Copy)]
enum Acyc {
    /// order-encoded levels g_{v,j} = [level(v) >= j], j <= lmax (inputs at level 0);
    /// complete only when lmax bounds the depth of every program (lmax = cap always does)
    Levels(usize),
    /// a total order on the non-input vectors (one variable per pair, transitivity on
    /// every triple); each production puts its operands before its result -- no depth bound
    Order,
}

/// the feasibility question as a CNF (DIMACS): x_v selects vector v, y_p a production,
/// acyclicity by levels or by a total order (`Acyc`), a sequential counter for
/// sum x_v <= cap, plus the sound strengthenings y_p -> x_v, at most one production per
/// vector, and every selected non-target vector used.
/// Returns (text, variable index of x_v per vector).
fn feasibility_cnf(cat: &Catalog, cap: usize, acyc: Acyc) -> (String, Vec<usize>) {
    let d = cat.n;
    let mut nv = 0usize;
    let mut fresh = || {
        nv += 1;
        nv
    };
    let mut xvar = vec![0usize; d];
    for v in N..d {
        xvar[v] = fresh();
    }
    let mut prods: Vec<(usize, usize, Option<usize>)> = Vec::new();
    for v in N..d {
        for p in &cat.opts[v] {
            prods.push((v, p.u as usize, if p.v == NONE { None } else { Some(p.v as usize) }));
        }
    }
    let yvar: Vec<usize> = prods.iter().map(|_| fresh()).collect();
    let mut clauses: Vec<Vec<i64>> = Vec::new();
    // inputs and targets selected
    for v in N..d {
        if cat.required.get(v) {
            clauses.push(vec![xvar[v] as i64]);
        }
    }
    let mut by_v: Vec<Vec<usize>> = vec![Vec::new(); d];
    for (pi, &(v, u, w)) in prods.iter().enumerate() {
        by_v[v].push(pi);
        let y = yvar[pi] as i64;
        // operands selected
        if u >= N {
            clauses.push(vec![-y, xvar[u] as i64]);
        }
        if let Some(w) = w {
            if w >= N {
                clauses.push(vec![-y, xvar[w] as i64]);
            }
        }
    }
    let acyc_desc = match acyc {
        Acyc::Levels(lmax0) => {
            let lmax = lmax0.max(1);
            // levels: g[v][j], j = 1..=lmax, for non-inputs
            let mut g = vec![Vec::new(); d];
            for v in N..d {
                g[v] = (0..lmax).map(|_| fresh()).collect();
            }
            // level monotonicity: g_{v,j+1} -> g_{v,j}
            for v in N..d {
                for j in 1..lmax {
                    clauses.push(vec![-(g[v][j] as i64), g[v][j - 1] as i64]);
                }
            }
            for (pi, &(v, u, w)) in prods.iter().enumerate() {
                let y = yvar[pi] as i64;
                // level(v) > level(operand): y -> g_{v,1}; y & g_{u,j} -> g_{v,j+1}; y -> not g_{u,lmax}
                clauses.push(vec![-y, g[v][0] as i64]);
                for &o in [Some(u), w].iter().flatten() {
                    if o >= N {
                        for j in 1..lmax {
                            clauses.push(vec![-y, -(g[o][j - 1] as i64), g[v][j] as i64]);
                        }
                        clauses.push(vec![-y, -(g[o][lmax - 1] as i64)]);
                    }
                }
            }
            format!("lmax {}", lmax)
        }
        Acyc::Order => {
            // o[a][b] for a < b (non-input indices): "a is produced before b";
            // before(a, b) = o[a][b] if a < b, else not o[b][a]
            let m = d - N;
            let mut o = vec![0usize; m * m];
            for a in 0..m {
                for b in a + 1..m {
                    o[a * m + b] = fresh();
                }
            }
            let before = |a: usize, b: usize| -> i64 {
                if a < b {
                    o[a * m + b] as i64
                } else {
                    -(o[b * m + a] as i64)
                }
            };
            // transitivity: forbid both cyclic orientations of every triple
            for a in 0..m {
                for b in a + 1..m {
                    for c in b + 1..m {
                        let (ab, bc, ac) = (o[a * m + b] as i64, o[b * m + c] as i64, o[a * m + c] as i64);
                        clauses.push(vec![-ab, -bc, ac]);
                        clauses.push(vec![ab, bc, -ac]);
                    }
                }
            }
            // a selected production puts its non-input operands before its result
            for (pi, &(v, u, w)) in prods.iter().enumerate() {
                let y = yvar[pi] as i64;
                for &op in [Some(u), w].iter().flatten() {
                    if op >= N {
                        clauses.push(vec![-y, before(op - N, v - N)]);
                    }
                }
            }
            "order".to_string()
        }
    };
    // x_v -> some production
    for v in N..d {
        let mut c: Vec<i64> = vec![-(xvar[v] as i64)];
        for &pi in &by_v[v] {
            c.push(yvar[pi] as i64);
        }
        clauses.push(c);
    }
    // strengthenings, sound for the feasibility question: a closed set of <= cap vectors
    // has a derivation of the targets in which every vector used has exactly one
    // production, every production is of a selected vector, and every selected non-target
    // vector is an operand of some selected production (unused vectors can be dropped and
    // the rest stays closed and within the cap).  Hence: y_p -> x_v; at most one y_p per v
    // (ladder encoding); x_v -> target(v) or some selected production uses v.
    let mut used_by: Vec<Vec<usize>> = vec![Vec::new(); d];
    for (pi, &(v, u, w)) in prods.iter().enumerate() {
        clauses.push(vec![-(yvar[pi] as i64), xvar[v] as i64]);
        if u >= N {
            used_by[u].push(pi);
        }
        if let Some(w) = w {
            if w >= N && w != u {
                used_by[w].push(pi);
            }
        }
    }
    for v in N..d {
        let ys: Vec<i64> = by_v[v].iter().map(|&pi| yvar[pi] as i64).collect();
        if ys.len() <= 5 {
            for i in 0..ys.len() {
                for j in i + 1..ys.len() {
                    clauses.push(vec![-ys[i], -ys[j]]);
                }
            }
        } else {
            // s_i = [some of y_1..y_i is true]
            let s: Vec<usize> = (0..ys.len() - 1).map(|_| fresh()).collect();
            clauses.push(vec![-ys[0], s[0] as i64]);
            for i in 1..ys.len() {
                if i < ys.len() - 1 {
                    clauses.push(vec![-ys[i], s[i] as i64]);
                    clauses.push(vec![-(s[i - 1] as i64), s[i] as i64]);
                }
                clauses.push(vec![-ys[i], -(s[i - 1] as i64)]);
            }
        }
        if !cat.required.get(v) {
            let mut c: Vec<i64> = vec![-(xvar[v] as i64)];
            for &pi in &used_by[v] {
                c.push(yvar[pi] as i64);
            }
            clauses.push(c);
        }
    }
    // sequential counter: at most cap of the x_v (Sinz 2005)
    let xs: Vec<usize> = (N..d).map(|v| xvar[v]).collect();
    let n = xs.len();
    if n > cap {
        let mut sreg = vec![vec![0usize; cap]; n];
        for i in 0..n {
            for j in 0..cap {
                sreg[i][j] = fresh();
            }
        }
        for i in 0..n {
            let xi = xs[i] as i64;
            clauses.push(vec![-xi, sreg[i][0] as i64]);
            if i > 0 {
                for j in 0..cap {
                    clauses.push(vec![-(sreg[i - 1][j] as i64), sreg[i][j] as i64]);
                }
                for j in 1..cap {
                    clauses.push(vec![-xi, -(sreg[i - 1][j - 1] as i64), sreg[i][j] as i64]);
                }
                clauses.push(vec![-xi, -(sreg[i - 1][cap - 1] as i64)]);
            }
        }
    }
    let mut out = String::new();
    out.push_str(&format!("c lns48 feasibility: {} vectors ({} inputs), {} productions, cap {}, {}\n", d, N, prods.len(), cap, acyc_desc));
    out.push_str(&format!("p cnf {} {}\n", nv, clauses.len()));
    for c in &clauses {
        for l in c {
            out.push_str(&format!("{} ", l));
        }
        out.push_str("0\n");
    }
    (out, xvar)
}

/// read a DIMACS solver output ("s SATISFIABLE" / "v ..." lines); the selected set
fn read_model(path: &str, xvar: &[usize]) -> Option<Bits> {
    let text = std::fs::read_to_string(path).ok()?;
    if !text.lines().any(|l| l.starts_with("s SATISFIABLE")) {
        return None;
    }
    let mut truth: FxSet<i64> = FxSet::default();
    for l in text.lines().filter(|l| l.starts_with("v ")) {
        for tok in l[2..].split_whitespace() {
            if let Ok(x) = tok.parse::<i64>() {
                if x > 0 {
                    truth.insert(x);
                }
            }
        }
    }
    let mut sel = Bits::full(N);
    for (v, &xv) in xvar.iter().enumerate() {
        if v >= N && truth.contains(&(xv as i64)) {
            sel.set(v);
        }
    }
    Some(sel)
}

// ------------------------------------------------------------------ programs
/// a plan: produced values in order with their productions (as vectors)
#[derive(Clone)]
struct Plan {
    steps: Vec<(V, ProdV)>,
}

fn plan_from_trace(cat: &Catalog, dict: &Dict, trace: &[(usize, usize)]) -> Plan {
    let mut steps = Vec::new();
    for &(x, k) in trace {
        let p = cat.opts[x][k];
        let u = dict.vals[p.u as usize];
        let pv = if p.v == NONE {
            ProdV { u, v: None, a: 0, b: 0, num: p.num as i64, den: p.den as i64 }
        } else {
            ProdV { u, v: Some(dict.vals[p.v as usize]), a: p.a as i64, b: p.b as i64, num: 0, den: 0 }
        };
        steps.push((dict.vals[x], pv));
    }
    Plan { steps }
}

fn plan_cost(plan: &Plan) -> usize {
    plan.steps.len()
}

/// emit PLinOpt/SLPchecker syntax; returns (text, adds, scalings)
fn emit(plan: &Plan, targets: &[V]) -> (String, usize, usize) {
    // each stored signal is sigma * (canonical direction); signs are chosen so
    // that no binary operation needs both operands negated and no scaling is
    // negative (free in PLinOpt's count, but Patel's model charges them)
    let mut names: FxMap<V, (String, i64)> = FxMap::default();
    for j in 0..N {
        names.insert(unit(j), (format!("i{}", j), 1));
    }
    // preferred stored sign of a target direction: the target's own sign
    let mut want: FxMap<V, i64> = FxMap::default();
    for tv in targets {
        if !is_zero(tv) {
            let (c, sg) = canon(tv);
            want.entry(c).or_insert(sg);
        }
    }
    let mut out = String::new();
    let (mut adds, mut scalings) = (0, 0);
    for (t, (x, p)) in plan.steps.iter().enumerate() {
        let name = format!("t{}", t + 1);
        let pref = *want.get(x).unwrap_or(&1);
        let (un, su) = names.get(&p.u).expect("operand defined").clone();
        let (rhs, sx) = match &p.v {
            None => {
                scalings += 1;
                let c_neg = (p.num < 0) != (su < 0);
                let (num, den) = (p.num.abs(), p.den);
                let r = if den == 1 {
                    format!("{}*{}", un, num)
                } else if num == 1 {
                    format!("{}/{}", un, den)
                } else {
                    format!("{}*{}/{}", un, num, den)
                };
                (r, if c_neg { -1 } else { 1 })
            }
            Some(v) => {
                adds += 1;
                let (vn, sv) = names.get(v).expect("operand defined").clone();
                let (ca, cb) = (p.a * su, p.b * sv);
                match (ca > 0, cb > 0) {
                    (true, true) => (format!("{}+{}", un, vn), 1),
                    (false, false) => (format!("{}+{}", un, vn), -1),
                    // a single subtraction can be written either way round: take the target's sign
                    (true, false) => (if pref > 0 { format!("{}-{}", un, vn) } else { format!("{}-{}", vn, un) }, pref),
                    (false, true) => (if pref > 0 { format!("{}-{}", vn, un) } else { format!("{}-{}", un, vn) }, pref),
                }
            }
        };
        out.push_str(&format!("{}:={};\n", name, rhs));
        names.insert(*x, (name, sx));
    }
    for (k, tv) in targets.iter().enumerate() {
        if is_zero(tv) {
            out.push_str(&format!("o{}:=0;\n", k));
            continue;
        }
        let (c, s) = canon(tv);
        let (nm, sx) = names.get(&c).expect("target produced");
        out.push_str(&format!("o{}:={}{};\n", k, if s * sx < 0 { "-" } else { "" }, nm));
    }
    (out, adds, scalings)
}

// ------------------------------------------------------------------ SLP parsing
#[derive(Clone, Debug)]
enum Lin {
    Const(i64, i64), // num/den
    Vec(V),
}

struct Parser<'a> {
    s: &'a [u8],
    i: usize,
    env: &'a FxMap<String, V>,
    nodes: Vec<(V, ProdV)>, // charged nodes in evaluation order
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<u8> {
        self.s.get(self.i).copied()
    }
    fn skip_ws(&mut self) {
        while matches!(self.peek(), Some(b' ') | Some(b'\t') | Some(b'\n') | Some(b'\r')) {
            self.i += 1;
        }
    }
    fn expr(&mut self) -> Result<Lin, String> {
        let mut acc = self.term()?;
        loop {
            self.skip_ws();
            match self.peek() {
                Some(b'+') | Some(b'-') => {
                    let op = self.peek().unwrap();
                    self.i += 1;
                    let rhs = self.term()?;
                    acc = self.combine(acc, rhs, if op == b'+' { 1 } else { -1 })?;
                }
                _ => return Ok(acc),
            }
        }
    }
    fn combine(&mut self, l: Lin, r: Lin, sg: i64) -> Result<Lin, String> {
        match (l, r) {
            (Lin::Const(a, b), Lin::Const(c, d)) => {
                let num = a * d + sg * c * b;
                let den = b * d;
                let g = gcd(num, den).max(1);
                Ok(Lin::Const(num / g, den / g))
            }
            (Lin::Vec(u), Lin::Vec(v)) => {
                let r = if sg > 0 { vadd(&u, &v) } else { vsub(&u, &v) };
                if !in_range(&r) {
                    return Err("value out of range".into());
                }
                self.nodes.push((r, ProdV { u, v: Some(v), a: 1, b: sg, num: 0, den: 0 }));
                Ok(Lin::Vec(r))
            }
            _ => Err("affine expression".into()),
        }
    }
    fn term(&mut self) -> Result<Lin, String> {
        let mut acc = self.factor()?;
        loop {
            self.skip_ws();
            match self.peek() {
                Some(b'*') | Some(b'/') => {
                    let op = self.peek().unwrap();
                    self.i += 1;
                    let rhs = self.factor()?;
                    acc = match (acc, rhs, op) {
                        (Lin::Const(a, b), Lin::Const(c, d), b'*') => Lin::Const(a * c, b * d),
                        (Lin::Const(a, b), Lin::Const(c, d), _) => Lin::Const(a * d, b * c),
                        (Lin::Vec(u), Lin::Const(c, d), b'*') => self.scaled(u, c, d)?,
                        (Lin::Vec(u), Lin::Const(c, d), _) => self.scaled(u, d, c)?,
                        (Lin::Const(c, d), Lin::Vec(u), b'*') => self.scaled(u, c, d)?,
                        _ => return Err("nonlinear term".into()),
                    };
                }
                _ => return Ok(acc),
            }
        }
    }
    fn scaled(&mut self, u: V, num: i64, den: i64) -> Result<Lin, String> {
        if den == 0 {
            return Err("division by zero".into());
        }
        let g = gcd(num, den).max(1);
        let (mut num, mut den) = (num / g, den / g);
        if den < 0 {
            num = -num;
            den = -den;
        }
        let r = vscale(&u, num, den).ok_or("scaling not representable over 1/64")?;
        if num.abs() != 1 || den != 1 {
            self.nodes.push((r, ProdV { u, v: None, a: 0, b: 0, num, den }));
        }
        Ok(Lin::Vec(r))
    }
    fn factor(&mut self) -> Result<Lin, String> {
        self.skip_ws();
        match self.peek() {
            Some(b'-') => {
                self.i += 1;
                let f = self.factor()?;
                Ok(match f {
                    Lin::Const(a, b) => Lin::Const(-a, b),
                    Lin::Vec(u) => Lin::Vec(vsub(&[0; N], &u)),
                })
            }
            Some(b'+') => {
                self.i += 1;
                self.factor()
            }
            Some(b'(') => {
                self.i += 1;
                let e = self.expr()?;
                self.skip_ws();
                if self.peek() != Some(b')') {
                    return Err("expected )".into());
                }
                self.i += 1;
                Ok(e)
            }
            Some(c) if c.is_ascii_digit() => {
                let st = self.i;
                while matches!(self.peek(), Some(c) if c.is_ascii_digit()) {
                    self.i += 1;
                }
                let n: i64 = std::str::from_utf8(&self.s[st..self.i]).unwrap().parse().unwrap();
                Ok(Lin::Const(n, 1))
            }
            Some(c) if c.is_ascii_alphabetic() || c == b'_' => {
                let st = self.i;
                while matches!(self.peek(), Some(c) if c.is_ascii_alphanumeric() || c == b'_') {
                    self.i += 1;
                }
                let name = std::str::from_utf8(&self.s[st..self.i]).unwrap();
                if let Some(v) = self.env.get(name) {
                    Ok(Lin::Vec(*v))
                } else if let Some(j) = name.strip_prefix('i').and_then(|t| t.parse::<usize>().ok()) {
                    if j < N { Ok(Lin::Vec(unit(j))) } else { Err(format!("input {} beyond {}", name, N)) }
                } else {
                    Err(format!("undefined {}", name))
                }
            }
            _ => Err(format!("unexpected character at {}", self.i)),
        }
    }
}

struct Program {
    targets: Vec<V>,          // o0.. in order (actual vectors, signed)
    values: Vec<V>,           // every charged node's direction (deduplicated), plus targets
    witness: FxMap<V, ProdV>, // production of each value in the seed program
}

fn parse_slp(text: &str) -> Result<Program, String> {
    let mut env: FxMap<String, V> = FxMap::default();
    let mut outputs: Vec<(usize, V)> = Vec::new();
    let mut values: Vec<V> = Vec::new();
    let mut seen: FxSet<V> = FxSet::default();
    let mut witness: FxMap<V, ProdV> = FxMap::default();
    let body: String = text.lines().map(|l| l.split('#').next().unwrap_or("")).collect::<Vec<_>>().join("\n");
    for stmt in body.split(';') {
        let stmt = stmt.trim();
        if stmt.is_empty() {
            continue;
        }
        let (lhs, rhs) = stmt.split_once(":=").ok_or(format!("bad statement {:?}", stmt))?;
        let lhs = lhs.trim();
        let val = {
            let mut p = Parser { s: rhs.as_bytes(), i: 0, env: &env, nodes: Vec::new() };
            let e = p.expr()?;
            p.skip_ws();
            if p.i != p.s.len() {
                return Err(format!("trailing input in {:?}", stmt));
            }
            for (v, pv) in p.nodes {
                let c = canon(&v).0;
                if !is_zero(&c) && c.iter().enumerate().filter(|(_, x)| **x != 0).count() > 0 {
                    if seen.insert(c) {
                        values.push(c);
                    }
                    witness.entry(c).or_insert(pv);
                }
            }
            match e {
                Lin::Vec(v) => v,
                Lin::Const(..) => return Err(format!("scalar statement {:?}", stmt)),
            }
        };
        if let Some(k) = lhs.strip_prefix('o').and_then(|t| t.parse::<usize>().ok()) {
            outputs.push((k, val));
        }
        env.insert(lhs.to_string(), val);
    }
    outputs.sort_by_key(|(k, _)| *k);
    for (i, (k, _)) in outputs.iter().enumerate() {
        if *k != i {
            return Err("outputs not contiguous".into());
        }
    }
    let targets: Vec<V> = outputs.into_iter().map(|(_, v)| v).collect();
    for t in &targets {
        let c = canon(t).0;
        if !is_zero(&c) && seen.insert(c) {
            values.push(c);
        }
    }
    Ok(Program { targets, values, witness })
}

/// evaluate an emitted program and return its outputs (for self-verification)
fn eval_outputs(text: &str) -> Result<Vec<V>, String> {
    Ok(parse_slp(text)?.targets)
}

fn read_sms(path: &str) -> Vec<V> {
    let text = std::fs::read_to_string(path).expect("sms readable");
    let mut rows: Vec<V> = Vec::new();
    let mut header = true;
    for ln in text.lines() {
        let p: Vec<&str> = ln.split_whitespace().collect();
        if header {
            if p.len() >= 2 {
                if let (Ok(r), Ok(c)) = (p[0].parse::<usize>(), p[1].parse::<usize>()) {
                    assert!(c == N, "sms must have {} columns (got {})", N, c);
                    rows = vec![[0; N]; r];
                    header = false;
                }
            }
            continue;
        }
        if p.len() < 3 || (p[0] == "0" && p[1] == "0") {
            break;
        }
        let (i, j) = (p[0].parse::<usize>().unwrap() - 1, p[1].parse::<usize>().unwrap() - 1);
        let (num, den) = match p[2].split_once('/') {
            Some((a, b)) => (a.parse::<i64>().unwrap(), b.parse::<i64>().unwrap()),
            None => (p[2].parse::<i64>().unwrap(), 1),
        };
        assert!((num * SCAL) % den == 0, "entry {} not over 1/64", p[2]);
        rows[i][j] = num * SCAL / den;
    }
    rows
}

/// a naive chain program for a matrix: each row as a left-to-right chain of
/// (scaled) inputs; its value set is closed by construction
fn naive_program(rows: &[V]) -> Program {
    let mut values = Vec::new();
    let mut seen: FxSet<V> = FxSet::default();
    let mut witness: FxMap<V, ProdV> = FxMap::default();
    let mut push = |v: V, pv: Option<ProdV>, values: &mut Vec<V>| {
        let c = canon(&v).0;
        if !is_zero(&c) && seen.insert(c) {
            values.push(c);
            if let Some(p) = pv {
                witness.insert(c, p);
            }
        }
    };
    for row in rows {
        let mut acc: Option<V> = None;
        for j in 0..N {
            if row[j] == 0 {
                continue;
            }
            let g = gcd(row[j], SCAL);
            let term = vscale(&unit(j), row[j] / g, SCAL / g).unwrap(); // the signed, scaled input
            if row[j].abs() != SCAL {
                push(term, Some(ProdV { u: unit(j), v: None, a: 0, b: 0, num: row[j] / g, den: SCAL / g }), &mut values);
            }
            acc = Some(match acc {
                None => term,
                Some(a) => {
                    let s = vadd(&a, &term);
                    push(s, Some(ProdV { u: a, v: Some(term), a: 1, b: 1, num: 0, den: 0 }), &mut values);
                    s
                }
            });
        }
    }
    Program { targets: rows.to_vec(), values, witness }
}

// ------------------------------------------------------------------ proposals
const FAMILIES: [&str; 6] = ["target_residual", "coordinated", "sparse_pivot", "internal_residual", "dyadic", "broad"];
const WEIGHTS: [f64; 6] = [30.0, 25.0, 20.0, 10.0, 10.0, 5.0];

struct Proposals {
    targets: Vec<V>,                 // target directions that are not inputs
    consumers: FxMap<V, Vec<V>>,     // value -> values consuming it (plan DAG)
    non_targets: Vec<V>,             // produced values that are not targets
    cones: FxMap<V, FxSet<V>>,       // value -> downstream targets
    // cache for the current value set
    cache_fp: u64,
    target_ranked: Vec<(V, f64)>,
    internal_hits: FxMap<V, FxSet<V>>,
    sparse: Vec<V>,
    stats: [[u64; 5]; 6], // draws, packages, directions, empty, unreachable
}

impl Proposals {
    fn new(plan: &Plan, targets: &[V]) -> Proposals {
        let tdirs: FxSet<V> = targets.iter().filter(|t| !is_zero(t)).map(|t| canon(t).0).collect();
        let mut consumers: FxMap<V, Vec<V>> = FxMap::default();
        let mut producer: FxMap<V, &ProdV> = FxMap::default();
        for (x, p) in &plan.steps {
            producer.insert(*x, p);
            consumers.entry(canon(&p.u).0).or_default().push(*x);
            if let Some(v) = &p.v {
                consumers.entry(canon(v).0).or_default().push(*x);
            }
        }
        let mut cones: FxMap<V, FxSet<V>> = FxMap::default();
        for t in &tdirs {
            let mut stack = vec![*t];
            let mut seen: FxSet<V> = FxSet::default();
            while let Some(v) = stack.pop() {
                if !seen.insert(v) {
                    continue;
                }
                cones.entry(v).or_default().insert(*t);
                if let Some(p) = producer.get(&v) {
                    stack.push(canon(&p.u).0);
                    if let Some(w) = &p.v {
                        stack.push(canon(w).0);
                    }
                }
            }
        }
        let non_targets: Vec<V> = plan.steps.iter().map(|(x, _)| *x).filter(|x| !tdirs.contains(x)).collect();
        let targets: Vec<V> = tdirs.into_iter().filter(|t| t.iter().filter(|x| **x != 0).count() > 1 || t.iter().all(|x| *x == 0 || x.abs() != SCAL)).collect();
        Proposals {
            targets,
            consumers,
            non_targets,
            cones,
            cache_fp: 0,
            target_ranked: Vec::new(),
            internal_hits: FxMap::default(),
            sparse: Vec::new(),
            stats: [[0; 5]; 6],
        }
    }

    fn refresh(&mut self, values: &[V]) {
        let fp = fingerprint(values);
        if fp == self.cache_fp {
            return;
        }
        self.cache_fp = fp;
        let known: FxSet<V> = values.iter().copied().collect();
        let residuals = |consumers: &[V]| -> FxMap<V, FxSet<V>> {
            let mut hits: FxMap<V, FxSet<V>> = FxMap::default();
            for t in consumers {
                for v in values {
                    for c in [-1i64, 1] {
                        let q = if c > 0 { vadd(t, v) } else { vsub(t, v) };
                        if !in_range(&q) {
                            continue;
                        }
                        let q = canon(&q).0;
                        if !is_zero(&q) && !known.contains(&q) {
                            hits.entry(q).or_default().insert(*t);
                        }
                    }
                }
            }
            hits
        };
        let target_hits = residuals(&self.targets);
        let internal: Vec<V> = {
            let mut s: FxSet<V> = FxSet::default();
            for cs in self.consumers.values() {
                for x in cs {
                    s.insert(*x);
                }
            }
            s.into_iter().collect()
        };
        self.internal_hits = residuals(&internal);
        self.target_ranked = target_hits
            .iter()
            .filter(|(_, h)| h.len() >= 3)
            .map(|(q, h)| (*q, ((1 + h.len()) as f64).powi(2) / (1 + nnz(q)) as f64))
            .collect();
        self.target_ranked.sort_by(|a, b| a.0.cmp(&b.0));
        let mut sparse: FxSet<V> = FxSet::default();
        let inputs: Vec<V> = (0..N).map(unit).collect();
        for group in [&inputs, &self.targets] {
            for (ai, a) in group.iter().enumerate() {
                for b in &group[ai + 1..] {
                    for sg in [-1i64, 1] {
                        let q = if sg > 0 { vadd(a, b) } else { vsub(a, b) };
                        let q = canon(&q).0;
                        if !is_zero(&q) && !known.contains(&q) && nnz(&q) <= 4 && in_range(&q) {
                            sparse.insert(q);
                        }
                    }
                }
            }
        }
        self.sparse = sparse.into_iter().collect();
        self.sparse.sort();
    }

    fn weighted_pick(entries: &[(V, f64)], rng: &mut Rng) -> Option<V> {
        if entries.is_empty() {
            return None;
        }
        let w: Vec<f64> = entries.iter().map(|e| e.1).collect();
        Some(entries[rng.weighted(&w)].0)
    }

    fn residual_for(&self, cs: &[V], rng: &mut Rng) -> Option<V> {
        let cset: FxSet<V> = cs.iter().copied().collect();
        let mut entries: Vec<(V, f64)> = self
            .internal_hits
            .iter()
            .filter_map(|(q, h)| {
                let k = h.iter().filter(|t| cset.contains(*t)).count();
                if k > 0 { Some((*q, ((1 + k) as f64).powi(2) / (1 + nnz(q)) as f64)) } else { None }
            })
            .collect();
        entries.sort_by(|a, b| a.0.cmp(&b.0));
        Self::weighted_pick(&entries, rng)
    }

    fn package(&self, family: usize, values: &[V], rng: &mut Rng) -> Vec<V> {
        match family {
            0 => Self::weighted_pick(&self.target_ranked, rng).into_iter().collect(),
            2 => {
                if self.sparse.is_empty() { vec![] } else { vec![*rng.choose(&self.sparse)] }
            }
            3 => {
                let mut shared: Vec<(&V, &Vec<V>)> = self.consumers.iter().filter(|(_, cs)| cs.len() >= 2).collect();
                if shared.is_empty() {
                    return vec![];
                }
                shared.sort_by(|a, b| a.0.cmp(b.0));
                let w: Vec<f64> = shared.iter().map(|(_, cs)| cs.len() as f64).collect();
                let (_, cs) = shared[rng.weighted(&w)];
                self.residual_for(cs, rng).into_iter().collect()
            }
            1 => {
                let mut overlapping: Vec<(V, V)> = Vec::new();
                for (ai, a) in self.non_targets.iter().enumerate() {
                    for b in &self.non_targets[ai + 1..] {
                        if let (Some(ca), Some(cb)) = (self.cones.get(a), self.cones.get(b)) {
                            if ca.iter().any(|t| cb.contains(t)) {
                                overlapping.push((*a, *b));
                            }
                        }
                    }
                }
                if overlapping.is_empty() {
                    return vec![];
                }
                let (a, b) = *rng.choose(&overlapping);
                let mut selected = vec![a, b];
                if rng.f64() < 0.5 {
                    let third: Vec<V> = self
                        .non_targets
                        .iter()
                        .filter(|v| !selected.contains(v))
                        .filter(|v| {
                            let cv = self.cones.get(*v);
                            selected.iter().any(|u| match (cv, self.cones.get(u)) {
                                (Some(x), Some(y)) => x.iter().any(|t| y.contains(t)),
                                _ => false,
                            })
                        })
                        .copied()
                        .collect();
                    if !third.is_empty() {
                        selected.push(*rng.choose(&third));
                    }
                }
                let mut package = Vec::new();
                for u in &selected {
                    if let Some(cs) = self.consumers.get(u) {
                        if let Some(q) = self.residual_for(cs, rng) {
                            package.push(q);
                        }
                    }
                }
                package
            }
            _ => {
                let a = *rng.choose(values);
                let b = *rng.choose(values);
                let sg = rng.sign();
                let numerator = if sg > 0 { vadd(&a, &b) } else { vsub(&a, &b) };
                if family == 4 {
                    let known: FxSet<V> = values.iter().copied().collect();
                    let halves: Vec<V> = values.iter().filter(|v| vscale(v, 2, 1).map(|d| known.contains(&canon(&d).0)).unwrap_or(false)).copied().collect();
                    if !halves.is_empty() && rng.f64() < 0.5 {
                        let half = *rng.choose(&halves);
                        let numerator = match vscale(&half, 2, 1) {
                            Some(d) => d,
                            None => return vec![],
                        };
                        let a = *rng.choose(values);
                        let b = vsub(&numerator, &a);
                        return vec![b, numerator, half];
                    }
                    return match vscale(&numerator, 1, 2) {
                        Some(h) => vec![numerator, h],
                        None => vec![numerator],
                    };
                }
                match rng.below(5) {
                    0 => vec![numerator],
                    1 => match vscale(&numerator, 1, 2) {
                        Some(h) => vec![numerator, h],
                        None => vec![numerator],
                    },
                    2 => match vscale(&numerator, 2, 1) {
                        Some(d) => vec![numerator, d],
                        None => vec![numerator],
                    },
                    3 => match vscale(&b, 2, 1) {
                        Some(d) => {
                            let s = if sg > 0 { vadd(&a, &d) } else { vsub(&a, &d) };
                            vec![d, s]
                        }
                        None => vec![numerator],
                    },
                    _ => {
                        let c = *rng.choose(values);
                        let s = if rng.sign() > 0 { vadd(&numerator, &c) } else { vsub(&numerator, &c) };
                        vec![numerator, s]
                    }
                }
            }
        }
    }

    /// draw k new directions (as a reachable package set); returns (proposals, families used)
    fn draw(&mut self, values: &[V], targets: &Bits, rng: &mut Rng, k: usize) -> (Vec<V>, Vec<usize>) {
        self.refresh(values);
        let mut known: FxSet<V> = values.iter().copied().collect();
        let mut proposals: Vec<V> = Vec::new();
        let mut fams = Vec::new();
        let mut attempts = 0;
        while proposals.len() < k && attempts < 400 {
            attempts += 1;
            let family = rng.weighted(&WEIGHTS);
            self.stats[family][0] += 1;
            let package = self.package(family, values, rng);
            let mut new: Vec<V> = Vec::new();
            for v in package {
                if !in_range(&v) {
                    continue;
                }
                let q = canon(&v).0;
                if !is_zero(&q) && !known.contains(&q) && !new.contains(&q) {
                    new.push(q);
                }
            }
            if new.is_empty() {
                self.stats[family][3] += 1;
                continue;
            }
            if new.len() > k - proposals.len() {
                continue;
            }
            // the package must be reachable as a unit
            let mut d = Dict::new();
            for v in values.iter().chain(proposals.iter()).chain(new.iter()) {
                d.insert(v);
            }
            let reachable = match Catalog::build(&d, targets, &FxMap::default()) {
                Some(cat) => cat.closure(&Bits::full(d.vals.len()), None),
                None => false,
            };
            if !reachable {
                self.stats[family][4] += 1;
                continue;
            }
            for q in &new {
                known.insert(*q);
            }
            self.stats[family][1] += 1;
            self.stats[family][2] += new.len() as u64;
            proposals.extend(new);
            fams.push(family);
        }
        (proposals, fams)
    }
}

// ------------------------------------------------------------------ search
struct Search {
    targets: Vec<V>,
    current: Vec<V>, // directions (inputs included)
    current_cost: usize,
    current_plan: Plan,
    best_cost: usize,
    best_plan: Plan,
    proposals: Proposals,
    rng: Rng,
    reps: usize,
    temperature: f64,
    tabu: VecDeque<u64>,
    recent: FxSet<u64>,
    tabu_size: usize,
    kmax: usize,
    metropolis: bool,
    maxworse: usize,
    exact: bool,
    mip_time: f64,
    mip_solves: u64,
    iterations: u64,
    moves: [u64; 3], // descent, plateau, annealing
    improvements: u64,
}

fn target_bits(dict: &Dict, targets: &[V]) -> Bits {
    let mut b = Bits::default();
    for t in targets {
        if !is_zero(t) {
            let (i, _) = dict.get(t).expect("target in dictionary");
            b.set(i);
        }
    }
    b
}

impl Search {
    fn new(prog: &Program, seed: u64, reps: usize, temperature: f64, tabu_size: usize, kmax: usize, metropolis: bool, maxworse: usize, exact: bool, mip_time: f64) -> Search {
        let mut rng = Rng(seed.wrapping_mul(0x9e3779b97f4a7c15) ^ 0xd1b54a32d192ed03);
        let mut dict = Dict::new();
        for v in &prog.values {
            dict.insert(v);
        }
        for t in &prog.targets {
            dict.insert(t);
        }
        let tb = target_bits(&dict, &prog.targets);
        let cat = Catalog::build(&dict, &tb, &prog.witness).expect("seed dictionary within MAXD");
        assert!(cat.closure(&Bits::full(dict.vals.len()), None), "seed value set is not closed");
        let selected = reverse_delete(&cat, &mut rng, reps, &Bits::default());
        let mut trace = Vec::new();
        assert!(cat.closure(&selected, Some(&mut trace)));
        let plan = plan_from_trace(&cat, &dict, &trace);
        let cost = plan_cost(&plan);
        let current: Vec<V> = selected.iter().map(|i| dict.vals[i]).collect();
        let fp = fingerprint(&current);
        let proposals = Proposals::new(&plan, &prog.targets);
        let mut tabu = VecDeque::new();
        tabu.push_back(fp);
        let mut recent = FxSet::default();
        recent.insert(fp);
        Search {
            targets: prog.targets.clone(),
            current,
            current_cost: cost,
            current_plan: plan.clone(),
            best_cost: cost,
            best_plan: plan,
            proposals,
            rng,
            reps,
            temperature,
            tabu,
            recent,
            tabu_size,
            kmax,
            metropolis,
            maxworse,
            exact,
            mip_time,
            mip_solves: 0,
            iterations: 0,
            moves: [0; 3],
            improvements: 0,
        }
    }

    fn step(&mut self) -> bool {
        self.iterations += 1;
        let k = 1 + self.rng.below(self.kmax);
        let tdict_targets: Vec<V> = self.targets.clone();
        // dictionary of the current set, for the proposal reachability checks
        let mut d0 = Dict::new();
        for v in &self.current {
            d0.insert(v);
        }
        let tb0 = target_bits(&d0, &tdict_targets);
        let (proposals, _fams) = self.proposals.draw(&self.current, &tb0, &mut self.rng, k);
        if proposals.is_empty() {
            return false;
        }
        let mut dict = Dict::new();
        for v in &self.current {
            dict.insert(v);
        }
        let mut novel = Bits::default();
        for v in &proposals {
            let (i, _) = dict.insert(v);
            novel.set(i);
        }
        let tb = target_bits(&dict, &self.targets);
        let witness: FxMap<V, ProdV> = self.current_plan.steps.iter().map(|(x, p)| (*x, p.clone())).collect();
        let cat = match Catalog::build(&dict, &tb, &witness) {
            Some(c) => c,
            None => return false,
        };
        if !cat.closure(&Bits::full(dict.vals.len()), None) {
            return false;
        }
        let selected = if self.exact {
            self.mip_solves += 1;
            mip_select(&cat, self.mip_time).unwrap_or_else(|| reverse_delete(&cat, &mut self.rng, self.reps, &novel))
        } else {
            reverse_delete(&cat, &mut self.rng, self.reps, &novel)
        };
        let mut trace = Vec::new();
        assert!(cat.closure(&selected, Some(&mut trace)));
        let plan = plan_from_trace(&cat, &dict, &trace);
        let cost = plan_cost(&plan);
        let values: Vec<V> = selected.iter().map(|i| dict.vals[i]).collect();
        let fp = fingerprint(&values);
        let kind = if cost < self.current_cost {
            Some(0)
        } else if cost == self.current_cost && !self.recent.contains(&fp) {
            Some(1)
        } else if self.metropolis {
            // Metropolis on the current cost: worse sets accepted with probability
            // exp(-(cost - current) / T), but never beyond best + maxworse
            let d = (cost - self.current_cost) as f64;
            if cost <= self.best_cost + self.maxworse && !self.recent.contains(&fp) && self.temperature > 0.0 && self.rng.f64() < (-d / self.temperature).exp() {
                Some(2)
            } else {
                None
            }
        } else if cost == self.best_cost + 1 && !self.recent.contains(&fp) && self.temperature > 0.0 && self.rng.f64() < (-1.0 / self.temperature).exp() {
            Some(2)
        } else {
            None
        };
        if let Some(kd) = kind {
            self.moves[kd] += 1;
            self.current = values;
            self.current_cost = cost;
            self.current_plan = plan.clone();
            let stats = self.proposals.stats;
            self.proposals = Proposals::new(&self.current_plan, &self.targets);
            self.proposals.stats = stats;
            if self.recent.insert(fp) {
                self.tabu.push_back(fp);
                if self.tabu.len() > self.tabu_size {
                    if let Some(old) = self.tabu.pop_front() {
                        self.recent.remove(&old);
                    }
                }
            }
        }
        if cost < self.best_cost {
            self.best_cost = cost;
            self.best_plan = plan;
            self.improvements += 1;
        }
        kind.is_some()
    }
}

// ------------------------------------------------------------------ driver
fn opt(args: &mut Vec<String>, name: &str) -> Option<String> {
    if let Some(i) = args.iter().position(|a| a == name) {
        let v = args.get(i + 1).cloned();
        args.drain(i..i + 2);
        v
    } else {
        None
    }
}

fn verify_and_write(plan: &Plan, targets: &[V], path: &str) -> (usize, usize) {
    let (text, adds, scalings) = emit(plan, targets);
    let outs = eval_outputs(&text).expect("emitted program parses");
    assert!(outs.len() == targets.len() && outs.iter().zip(targets).all(|(a, b)| a == b), "emitted program does not compute the targets");
    assert!(adds + scalings == plan_cost(plan), "count mismatch");
    std::fs::write(path, text).expect("write program");
    (adds, scalings)
}

fn main() {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let slp = opt(&mut args, "--slp");
    let sms = opt(&mut args, "--sms");
    let out = opt(&mut args, "--out").expect("--out DIR");
    let wall: f64 = opt(&mut args, "--wall").map(|s| s.parse().unwrap()).unwrap_or(60.0);
    let seeds: usize = opt(&mut args, "--seeds").map(|s| s.parse().unwrap()).unwrap_or(4);
    let seed0: u64 = opt(&mut args, "--seed").map(|s| s.parse().unwrap()).unwrap_or(1);
    let temperature: f64 = opt(&mut args, "--temperature").map(|s| s.parse().unwrap()).unwrap_or(0.2);
    let tabu: usize = opt(&mut args, "--tabu").map(|s| s.parse().unwrap()).unwrap_or(256);
    let reps: usize = opt(&mut args, "--orders").map(|s| s.parse().unwrap()).unwrap_or(4);
    let log_every: f64 = opt(&mut args, "--log").map(|s| s.parse().unwrap()).unwrap_or(30.0);
    let kmax: usize = opt(&mut args, "--kmax").map(|s| s.parse().unwrap()).unwrap_or(8);
    let maxworse: usize = opt(&mut args, "--maxworse").map(|s| s.parse().unwrap()).unwrap_or(3);
    let mip_time: f64 = opt(&mut args, "--mip-time").map(|s| s.parse().unwrap()).unwrap_or(60.0);
    let exact = if let Some(i) = args.iter().position(|a| a == "--exact") {
        args.remove(i);
        true
    } else {
        false
    };
    let metropolis = if let Some(i) = args.iter().position(|a| a == "--metropolis") {
        args.remove(i);
        true
    } else {
        false
    };
    let merge = opt(&mut args, "--merge");
    let cap: Option<usize> = opt(&mut args, "--cap").map(|s| s.parse().unwrap());
    let propose: usize = opt(&mut args, "--propose").map(|s| s.parse().unwrap()).unwrap_or(0);
    let cnf_out = opt(&mut args, "--cnf");
    let universal: usize = opt(&mut args, "--universal").map(|s| s.parse().unwrap()).unwrap_or(0);
    let lmax_opt: Option<usize> = opt(&mut args, "--lmax").map(|s| s.parse().unwrap());
    let acyc_order = opt(&mut args, "--acyc").map(|s| s == "order").unwrap_or(false);
    let model_in = opt(&mut args, "--model");
    assert!(args.is_empty(), "unknown arguments: {:?}", args);
    std::fs::create_dir_all(&out).unwrap();

    // --merge A.slp,B.slp,...: union of the programs' signal sets (same targets), then the
    // exact minimum closed subset (MIP) and the greedy reverse deletion over that union
    if let Some(list) = merge {
        let mut progs = Vec::new();
        for path in list.split(',') {
            let text = std::fs::read_to_string(path).expect("slp readable");
            progs.push((path.to_string(), parse_slp(&text).unwrap_or_else(|e| panic!("parse {}: {}", path, e))));
        }
        // programs may have been optimized against sign-flipped copies of the same rows
        // (negations are free): compare target directions, emit the first program's signs
        let targets = progs[0].1.targets.clone();
        let dirs: Vec<V> = targets.iter().map(|t| canon(t).0).collect();
        for (path, p) in &progs {
            let d2: Vec<V> = p.targets.iter().map(|t| canon(t).0).collect();
            assert!(d2 == dirs, "{} has different targets (even up to sign)", path);
        }
        let mut dict = Dict::new();
        let mut witness: FxMap<V, ProdV> = FxMap::default();
        let mut costs = Vec::new();
        for (_, p) in &progs {
            let mut own = 0;
            for v in &p.values {
                let (i, _) = dict.insert(v);
                if i >= N {
                    own += 1;
                }
            }
            costs.push(own);
            for (k, w) in &p.witness {
                witness.entry(*k).or_insert(w.clone());
            }
        }
        for t in &targets {
            dict.insert(t);
        }
        if universal > 0 {
            // structured candidates: every sub-vector of <= `universal` terms of every target
            // (with the target's coefficients) and every pairwise sum/difference of targets
            let mut added = 0usize;
            let before = dict.vals.len();
            for t in &targets {
                let supp: Vec<usize> = (0..N).filter(|&j| t[j] != 0).collect();
                let m = supp.len();
                // subsets of size 1..=universal (and all sizes when the target has <= universal terms)
                for mask in 1u32..(1u32 << m) {
                    let size = mask.count_ones() as usize;
                    if size > universal || size == m {
                        continue;
                    }
                    let mut v = [0i64; N];
                    for (b, &j) in supp.iter().enumerate() {
                        if mask >> b & 1 == 1 {
                            v[j] = t[j];
                        }
                    }
                    dict.insert(&v);
                }
            }
            for (i, a) in targets.iter().enumerate() {
                for b in &targets[i + 1..] {
                    for (s_, w) in [(1, vadd(a, b)), (-1, vsub(a, b))] {
                        let _ = s_;
                        if !is_zero(&w) && in_range(&w) {
                            dict.insert(&w);
                        }
                    }
                }
            }
            added += dict.vals.len() - before;
            eprintln!("merge: universal dictionary added {} structured vectors (sub-vectors of <= {} terms, pairwise target sums/differences)", added, universal);
        }
        if propose > 0 {
            // a plan for the first program (its own closure order), to seed the proposal families
            let mut d0 = Dict::new();
            for v in &progs[0].1.values {
                d0.insert(v);
            }
            for t in &targets {
                d0.insert(t);
            }
            let tb0 = target_bits(&d0, &targets);
            let cat0 = Catalog::build(&d0, &tb0, &progs[0].1.witness).expect("first program within MAXD");
            let mut trace = Vec::new();
            assert!(cat0.closure(&Bits::full(d0.vals.len()), Some(&mut trace)));
            let plan0 = plan_from_trace(&cat0, &d0, &trace);
            let mut props = Proposals::new(&plan0, &targets);
            let mut rng = Rng(777);
            let mut current: Vec<V> = dict.vals.clone();
            let mut added = 0;
            while added < propose {
                let mut dcur = Dict::new();
                for v in &current {
                    dcur.insert(v);
                }
                let tbc = target_bits(&dcur, &targets);
                let (new, _) = props.draw(&current, &tbc, &mut rng, 8.min(propose - added));
                if new.is_empty() {
                    break;
                }
                for v in &new {
                    dict.insert(v);
                    current.push(*v);
                }
                added += new.len();
            }
            eprintln!("merge: added {} proposals from the six families", added);
        }
        let tb = target_bits(&dict, &targets);
        let cat = Catalog::build(&dict, &tb, &witness).expect("union dictionary within MAXD");
        assert!(cat.closure(&Bits::full(dict.vals.len()), None), "union not closed");
        let mut rng = Rng(12345);
        let greedy = reverse_delete(&cat, &mut rng, 8, &Bits::default());
        let gcost = greedy.count() - N;
        eprintln!("merge: {} programs with signal counts {:?}; union dictionary {} vectors; greedy minimum {}", progs.len(), costs, dict.vals.len(), gcost);
        if let Some(path) = &cnf_out {
            let c = cap.expect("--cnf needs --cap K");
            let acyc = if acyc_order { Acyc::Order } else { Acyc::Levels(lmax_opt.unwrap_or(c)) };
            let (text, xvar) = feasibility_cnf(&cat, c, acyc);
            std::fs::write(path, &text).expect("write cnf");
            let map: String = xvar.iter().enumerate().filter(|(v, _)| *v >= N).map(|(v, x)| format!("{} {}\n", v, x)).collect();
            std::fs::write(format!("{}.xvar", path), map).expect("write xvar map");
            let header = text.lines().nth(1).unwrap_or("").to_string();
            eprintln!("merge: wrote {} ({}) for the question: closed set of <= {} non-input signals?", path, header, c);
            if let Some(mpath) = &model_in {
                match read_model(mpath, &xvar) {
                    Some(sel) => {
                        if cat.closure(&sel, None) {
                            let mut trace = Vec::new();
                            assert!(cat.closure(&sel, Some(&mut trace)));
                            let plan = plan_from_trace(&cat, &dict, &trace);
                            let (a, sc) = verify_and_write(&plan, &targets, &format!("{}/best.slp", out));
                            println!("model result: closed set of {} = {} adds + {} scalings (cap {}) -> {}/best.slp", plan_cost(&plan), a, sc, c, out);
                        } else {
                            println!("model result: the model's selection is NOT closed (encoding bug?)");
                        }
                    }
                    None => println!("model result: no satisfying model in {}", mpath),
                }
            }
            return;
        }
        let t0 = Instant::now();
        let exact = match cap {
            Some(c) => {
                eprintln!("merge: feasibility question -- is there a closed set of at most {} non-input signals? (time limit {} s)", c, mip_time);
                mip_select_cap(&cat, mip_time, Some(c))
            }
            None => mip_select(&cat, mip_time),
        };
        if cap.is_some() && exact.is_none() {
            println!("merge result: no closed set of at most {} signals found over the union of {} programs (best single {}; MIP {:.0}s)", cap.unwrap(), progs.len(), costs.iter().min().unwrap(), t0.elapsed().as_secs_f64());
            return;
        }
        let (sel, label) = match exact {
            Some(s) => (s, "exact (MIP)"),
            None => (greedy, "greedy (MIP failed)"),
        };
        let mut trace = Vec::new();
        assert!(cat.closure(&sel, Some(&mut trace)));
        let plan = plan_from_trace(&cat, &dict, &trace);
        let (a, sc) = verify_and_write(&plan, &targets, &format!("{}/best.slp", out));
        println!(
            "merge result: {} minimum {} = {} adds + {} scalings over the union of {} programs (best single {}; MIP {:.0}s) -> {}/best.slp",
            label,
            plan_cost(&plan),
            a,
            sc,
            progs.len(),
            costs.iter().min().unwrap(),
            t0.elapsed().as_secs_f64(),
            out
        );
        return;
    }
    let prog = match (&slp, &sms) {
        (Some(p), _) => {
            let text = std::fs::read_to_string(p).expect("slp readable");
            let prog = parse_slp(&text).unwrap_or_else(|e| panic!("parse {}: {}", p, e));
            if let Some(m) = &sms {
                let rows = read_sms(m);
                assert!(rows == prog.targets, "seed program does not compute the matrix");
            }
            prog
        }
        (None, Some(m)) => naive_program(&read_sms(m)),
        _ => panic!("need --slp SEED.slp and/or --sms MATRIX.sms"),
    };
    let seed_cost = prog.values.iter().filter(|v| canon(v).0.iter().filter(|x| **x != 0).count() > 1 || v.iter().any(|x| *x != 0 && x.abs() != SCAL)).count();
    eprintln!(
        "lns48 (N = {}): {} targets, {} seed values (about {} ops), wall {}s x {} seeds, T {}, tabu {}, orders {}, kmax {}, metropolis {} (maxworse {}), exact {} (mip time {})",
        N,
        prog.targets.len(),
        prog.values.len(),
        seed_cost,
        wall,
        seeds,
        temperature,
        tabu,
        reps,
        kmax,
        metropolis,
        maxworse,
        exact,
        mip_time
    );
    let start = Instant::now();
    let results: Vec<(u64, usize, u64, Plan)> = std::thread::scope(|sc| {
        let handles: Vec<_> = (0..seeds)
            .map(|s| {
                let prog = &prog;
                let out = out.clone();
                sc.spawn(move || {
                    let seed = seed0 + s as u64;
                    let mut search = Search::new(prog, seed, reps, temperature, tabu, kmax, metropolis, maxworse, exact, mip_time);
                    let path = format!("{}/seed{}.slp", out, seed);
                    let (a, sc_) = verify_and_write(&search.best_plan, &search.targets, &path);
                    eprintln!("  seed {}: start {} = {}+{}", seed, search.best_cost, a, sc_);
                    let mut saved = search.best_cost;
                    let mut next_log = log_every;
                    while start.elapsed() < Duration::from_secs_f64(wall) {
                        search.step();
                        if search.best_cost < saved {
                            let (a, sc_) = verify_and_write(&search.best_plan, &search.targets, &path);
                            saved = search.best_cost;
                            eprintln!("  seed {}: {:7.1}s  best {} = {}+{}  (iteration {})", seed, start.elapsed().as_secs_f64(), saved, a, sc_, search.iterations);
                        }
                        let el = start.elapsed().as_secs_f64();
                        if el >= next_log {
                            eprintln!(
                                "  seed {}: {:.0}s best {} current {} iterations {} ({:.1}/s) moves d/p/a {:?} mip solves {}",
                                seed,
                                el,
                                search.best_cost,
                                search.current_cost,
                                search.iterations,
                                search.iterations as f64 / el,
                                search.moves,
                                search.mip_solves
                            );
                            next_log = el + log_every;
                        }
                    }
                    verify_and_write(&search.best_plan, &search.targets, &path);
                    (seed, search.best_cost, search.iterations, search.best_plan.clone())
                })
            })
            .collect();
        handles.into_iter().map(|h| h.join().unwrap()).collect()
    });
    let best = results.iter().min_by_key(|r| r.1).unwrap();
    let (a, s) = verify_and_write(&best.3, &prog.targets, &format!("{}/best.slp", out));
    let iters: u64 = results.iter().map(|r| r.2).sum();
    println!(
        "final: best {} = {} adds + {} scalings (seed {}); per seed {:?}; {} iterations in {:.0}s ({:.1}/s/thread) -> {}/best.slp",
        best.1,
        a,
        s,
        best.0,
        results.iter().map(|r| r.1).collect::<Vec<_>>(),
        iters,
        start.elapsed().as_secs_f64(),
        iters as f64 / start.elapsed().as_secs_f64() / seeds as f64,
        out
    );
    let _ = std::io::stdout().flush();
}
