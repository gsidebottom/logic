//! CNF -> AIG -> (ABC rewriting) -> CNF: circuit-aware preprocessing, native.
//!
//! The Rust port of `tools/cnf2aig.py` (same design, 20-50x faster on the
//! million-clause instances): the gate definitions read off the CNF -- AND/OR
//! of any width by clause pattern, XOR2/XOR3 by same-scope groups, and any
//! other function of up to three inputs by a truth-table check of the clauses
//! over a candidate scope -- become an And-Inverter Graph (inputs: the
//! undefined variables; outputs: the gate outputs that other clauses mention;
//! definition cycles are broken at one gate each, which stays in the residual;
//! unobserved cones are dropped).  ABC rewrites it, its cut-based CNF
//! generator writes it back, inputs and outputs keep their variable numbers,
//! the residual and the root units are appended.  Equisatisfiable by
//! construction.
//!
//!   cnf2aig in.cnf --out out.cnf --abc ABC [--script none|resyn2|resyn2f|dc2f|...]
//!   cnf2aig in.cnf --aag in.aig [--map in.map]   # the AIG only (binary AIGER), and the
//!                                                  # variable of each of its inputs and outputs
//!
//! Two modes need no ABC and carry a proof: `--recode out.cnf` (structural
//! hashing and dead cones) and `--sweep out.cnf` (SAT sweeping: functional
//! equivalences found by simulation, each proved by CaDiCaL).  With `--proof
//! prefix.drat` they write a DRAT prefix that derives the output from the
//! input; followed by a solver's proof of the output it refutes the input.
//!
//!   cnf2aig in.cnf --sweep out.cnf --proof prefix.drat
//!           [--rounds 16] [--first 64] [--window GATES] [--conflicts 1000] [--tries 2]
//!           [--recycle 1000] [--seconds S] [--order level|depth] [--give-up 32]
//!
//! (--give-up: a class of candidates is left alone after that many attempts
//! in a row ran out of budget.)
use logic::cadical::solver::Solver;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::io::Write;
use std::process::Command;

// ── clauses: flat storage, literals as DIMACS ints ────────────────────────

struct Cnf {
    nv: usize,
    lits: Vec<i32>,
    start: Vec<usize>, // clause i = lits[start[i]..start[i+1]]
}

impl Cnf {
    fn len(&self) -> usize { self.start.len() - 1 }
    fn clause(&self, i: usize) -> &[i32] { &self.lits[self.start[i]..self.start[i + 1]] }
}

fn parse_dimacs(bytes: &[u8]) -> Result<Cnf, String> {
    let mut nv = 0usize;
    let mut lits: Vec<i32> = Vec::new();
    let mut start = vec![0usize];
    let mut i = 0;
    let n = bytes.len();
    while i < n {
        let b = bytes[i];
        if b == b'c' {
            while i < n && bytes[i] != b'\n' { i += 1; }
            continue;
        }
        if b == b'p' {
            let e = bytes[i..].iter().position(|&x| x == b'\n').map(|p| i + p).unwrap_or(n);
            let line = std::str::from_utf8(&bytes[i..e]).map_err(|e| e.to_string())?;
            let f: Vec<&str> = line.split_whitespace().collect();
            if f.len() >= 4 { nv = f[2].parse().map_err(|_| "bad p line".to_string())?; }
            i = e;
            continue;
        }
        if b.is_ascii_whitespace() { i += 1; continue; }
        // an integer
        let mut neg = false;
        if b == b'-' { neg = true; i += 1; }
        let mut v: i64 = 0;
        while i < n && bytes[i].is_ascii_digit() { v = v * 10 + (bytes[i] - b'0') as i64; i += 1; }
        if v == 0 { start.push(lits.len()); } else { lits.push(if neg { -(v as i32) } else { v as i32 }); nv = nv.max(v as usize); }
    }
    if *start.last().unwrap() != lits.len() { start.push(lits.len()); } // a last clause without its 0
    Ok(Cnf { nv, lits, start })
}

fn write_cnf(path: &str, nv: usize, cls: &[Vec<i32>]) -> Result<(), String> {
    let f = std::fs::File::create(path).map_err(|e| e.to_string())?;
    let mut w = std::io::BufWriter::with_capacity(1 << 20, f);
    writeln!(w, "p cnf {} {}", nv, cls.len()).map_err(|e| e.to_string())?;
    let mut line = String::new();
    for c in cls {
        line.clear();
        for l in c { let _ = write!(line, "{} ", l); }
        line.push_str("0\n");
        w.write_all(line.as_bytes()).map_err(|e| e.to_string())?;
    }
    w.flush().map_err(|e| e.to_string())
}

/// Sort by variable and drop repeated literals; true for a tautology.  (By
/// value a literal and its negation are not neighbours.)
fn normalize(c: &mut Vec<i32>) -> bool {
    c.sort_unstable_by_key(|l| (l.unsigned_abs(), *l));
    c.dedup();
    c.windows(2).any(|w| w[0] == -w[1])
}

// ── root simplification: units to a fixpoint, tautologies out ─────────────

struct Root {
    cls: Vec<Vec<i32>>,
    origin: Vec<usize>, // cls[j] came from the input clause origin[j]
    units: Vec<i32>,
    unsat: bool,
}

fn simplify_root(cnf: &Cnf) -> Root {
    // linear unit propagation over occurrence lists; tautologies dropped
    let nv = cnf.nv;
    let n = cnf.len();
    let mut val: Vec<i8> = vec![0; nv + 1];
    let mut units: Vec<i32> = Vec::new();
    let mut alive: Vec<bool> = vec![true; n];
    let mut nfree: Vec<u32> = vec![0; n];
    // each clause's distinct literals (a repeated literal would be counted twice)
    let mut dedup: Vec<Vec<i32>> = Vec::with_capacity(n);
    let mut occ_start: Vec<usize> = vec![0; nv + 2];
    for (i, a) in alive.iter_mut().enumerate() {
        let mut c: Vec<i32> = cnf.clause(i).to_vec();
        let taut = normalize(&mut c);
        if taut { *a = false; c.clear(); }
        for &l in &c { occ_start[l.unsigned_abs() as usize + 1] += 1; }
        dedup.push(c);
    }
    for v in 1..=nv + 1 { occ_start[v] += occ_start[v - 1]; }
    let mut occ: Vec<u32> = vec![0; occ_start[nv + 1]];
    let mut fill = occ_start.clone();
    for (i, c) in dedup.iter().enumerate() {
        nfree[i] = c.len() as u32;
        for &l in c { let v = l.unsigned_abs() as usize; occ[fill[v]] = i as u32; fill[v] += 1; }
    }
    let mut queue: Vec<i32> = Vec::new();
    let mut unsat = false;
    let assign = |l: i32, val: &mut Vec<i8>, units: &mut Vec<i32>, queue: &mut Vec<i32>| -> bool {
        let v = l.unsigned_abs() as usize; let s: i8 = if l > 0 { 1 } else { -1 };
        if val[v] == 0 { val[v] = s; units.push(l); queue.push(l); true } else { val[v] == s }
    };
    for (i, &a) in alive.iter().enumerate() { if a && dedup[i].len() == 1 && !assign(dedup[i][0], &mut val, &mut units, &mut queue) { unsat = true; } }
    let mut qi = 0;
    while qi < queue.len() && !unsat {
        let l = queue[qi]; qi += 1;
        let v = l.unsigned_abs() as usize;
        for &ci in &occ[occ_start[v]..occ_start[v + 1]] {
            let i = ci as usize;
            if !alive[i] { continue; }
            let c = &dedup[i];
            if c.contains(&l) { alive[i] = false; continue; }   // satisfied
            nfree[i] -= 1;
            if nfree[i] == 0 { unsat = true; break; }
            if nfree[i] == 1 {
                // the one literal not yet processed: free, or already true and
                // still in the queue (then the clause is satisfied)
                let mut rem = None; let mut sat = false;
                for &x in c {
                    let vv = val[x.unsigned_abs() as usize];
                    if vv == 0 { rem = Some(x); } else if (x > 0) == (vv > 0) { sat = true; break; }
                }
                alive[i] = false;
                if sat { continue; }
                match rem {
                    Some(x) => { if !assign(x, &mut val, &mut units, &mut queue) { unsat = true; break; } }
                    None => { unsat = true; break; }
                }
            }
        }
    }
    if unsat { return Root { cls: Vec::new(), origin: Vec::new(), units, unsat: true }; }
    let mut cls: Vec<Vec<i32>> = Vec::new();
    let mut origin: Vec<usize> = Vec::new();
    for (i, &a) in alive.iter().enumerate() {
        if !a { continue; }
        let c = &dedup[i];
        let keep: Vec<i32> = c.iter().copied().filter(|&x| val[x.unsigned_abs() as usize] == 0).collect();
        if keep.len() >= 2 { cls.push(keep); origin.push(i); }
    }
    Root { cls, origin, units, unsat: false }
}

// ── gates ─────────────────────────────────────────────────────────────────

#[derive(Clone)]
struct Gate {
    out: u32,
    inputs: Vec<i32>,   // literals for AND (fn = all inputs true, output 'pos'); variables otherwise
    clauses: Vec<usize>,
    kind: Kind,
}

#[derive(Clone)]
enum Kind {
    And { pos: bool },             // out = AND(inputs) if pos else NOT AND(inputs)
    Table(Vec<bool>),              // out = table[row], row = input bits, first input most significant
}

fn scope_key(c: &[i32]) -> Vec<u32> {
    let mut s: Vec<u32> = c.iter().map(|l| l.unsigned_abs()).collect();
    s.sort_unstable();
    s.dedup();
    s
}

/// AND/OR of any width (a wide clause plus its binaries) and, when `xor` is
/// set, XOR2/XOR3 same-scope groups oriented towards their highest variable.
fn extract_pattern(cls: &[Vec<i32>], xor: bool) -> Vec<Gate> {
    let mut binset: HashMap<(i32, i32), usize> = HashMap::new();
    for (i, c) in cls.iter().enumerate() {
        if c.len() == 2 {
            let k = if c[0] < c[1] { (c[0], c[1]) } else { (c[1], c[0]) };
            binset.entry(k).or_insert(i);
        }
    }
    let mut defined: HashSet<u32> = HashSet::new();
    let mut gates = Vec::new();
    for (i, c) in cls.iter().enumerate() {
        if c.len() < 3 { continue; }
        for &o in c {
            if defined.contains(&o.unsigned_abs()) { continue; }
            let mut bins = Vec::with_capacity(c.len() - 1);
            let mut ok = true;
            for &l in c {
                if l == o { continue; }
                let (a, b) = if -o < -l { (-o, -l) } else { (-l, -o) };
                match binset.get(&(a, b)) { Some(&j) => bins.push(j), None => { ok = false; break; } }
            }
            if !ok { continue; }
            let ins: Vec<i32> = c.iter().filter(|&&l| l != o).map(|&l| -l).collect();
            let mut clauses = vec![i];
            clauses.extend(bins);
            gates.push(Gate { out: o.unsigned_abs(), inputs: ins, clauses, kind: Kind::And { pos: o > 0 } });
            defined.insert(o.unsigned_abs());
            break;
        }
    }
    if xor {
        let mut by_scope: HashMap<Vec<u32>, Vec<usize>> = HashMap::new();
        for (i, c) in cls.iter().enumerate() {
            if c.len() == 3 || c.len() == 4 { by_scope.entry(scope_key(c)).or_default().push(i); }
        }
        let mut keys: Vec<&Vec<u32>> = by_scope.keys().collect();
        keys.sort();
        for scope in keys {
            let idxs = &by_scope[scope];
            let k = scope.len();
            let want = if k == 3 { 4 } else { 8 };
            let group: Vec<&Vec<i32>> = idxs.iter().map(|&i| &cls[i]).filter(|c| c.len() == k).collect();
            if group.len() != want || idxs.len() != want { continue; }
            let par: HashSet<usize> = group.iter().map(|c| c.iter().filter(|&&l| l > 0).count() % 2).collect();
            if par.len() != 1 { continue; }
            let p = *par.iter().next().unwrap();
            let out = *scope.iter().max().unwrap();
            if defined.contains(&out) { continue; }
            let ins: Vec<i32> = scope.iter().filter(|&&v| v != out).map(|&v| v as i32).collect();
            // a clause forbids the assignment where all its literals are false: the
            // number of true variables there is (k - #positive) == k - p (mod 2);
            // the allowed rows have the other parity: out = parity(inputs) xor c
            // each clause forbids the row where all its literals are false, i.e.
            // where the number of true variables is the number of negative
            // literals, k - p; so the forbidden rows have (#true) == k - p (mod 2)
            // and out = 1 is allowed exactly when ones(inputs) == k - p (mod 2)
            let m = ins.len();
            let mut table = vec![false; 1 << m];
            for (row, slot) in table.iter_mut().enumerate() {
                let ones = (row as u32).count_ones() as usize;
                *slot = ones % 2 == (k + 2 - p) % 2;
            }
            gates.push(Gate { out, inputs: ins, clauses: idxs.clone(), kind: Kind::Table(table) });
            defined.insert(out);
        }
    }
    gates
}

/// Any function of up to three inputs, whatever the encoding: the clauses over
/// a candidate scope {o} + In are a definition when, by truth table, every
/// input row leaves exactly one value of o and none of them constrains the
/// inputs.  Candidates fewest-occurrences-first, small subsets of the most
/// co-occurring variables, largest first.
fn extract_generic(cls: &[Vec<i32>], gates: &mut Vec<Gate>, max_inputs: usize) {
    let mut defined: HashSet<u32> = gates.iter().map(|g| g.out).collect();
    let mut used: Vec<bool> = vec![false; cls.len()];
    for g in gates.iter() { for &i in &g.clauses { used[i] = true; } }
    let nv = cls.iter().flat_map(|c| c.iter()).map(|l| l.unsigned_abs()).max().unwrap_or(0) as usize;
    let mut occ: Vec<Vec<u32>> = vec![Vec::new(); nv + 1];
    for (i, c) in cls.iter().enumerate() {
        if used[i] || c.len() > 4 { continue; }
        for &l in c { occ[l.unsigned_abs() as usize].push(i as u32); }
    }
    // ties broken by first appearance in the clause list, as the Python tool does
    let mut first: Vec<u32> = vec![u32::MAX; nv + 1];
    for (i, c) in cls.iter().enumerate() { for &l in c { let v = l.unsigned_abs() as usize; if first[v] == u32::MAX { first[v] = i as u32; } } }
    let mut order: Vec<u32> = (1..=nv as u32).filter(|&v| !occ[v as usize].is_empty()).collect();
    order.sort_by_key(|&v| (occ[v as usize].len(), first[v as usize]));
    let mut cnt: HashMap<u32, u32> = HashMap::new();
    let mut seen_order: Vec<u32> = Vec::new();
    for &o in &order {
        if defined.contains(&o) { continue; }
        let idxs: Vec<u32> = occ[o as usize].iter().copied().filter(|&i| !used[i as usize]).collect();
        if idxs.is_empty() { continue; }
        cnt.clear(); seen_order.clear();
        for &i in &idxs { for &l in &cls[i as usize] { let v = l.unsigned_abs(); if v != o { let e = cnt.entry(v).or_insert(0); if *e == 0 { seen_order.push(v); } *e += 1; } } }
        let mut ranked: Vec<(u32, u32, u32)> = seen_order.iter().enumerate().map(|(k, &v)| (v, cnt[&v], k as u32)).collect();
        ranked.sort_by(|a, b| b.1.cmp(&a.1).then(a.2.cmp(&b.2)));
        let cand: Vec<u32> = ranked.iter().take(max_inputs + 2).map(|p| p.0).collect();
        let mut tried: HashSet<Vec<u32>> = HashSet::new();
        let mut hit: Option<(Vec<u32>, Vec<usize>, Vec<bool>)> = None;
        'search: for k in (1..=max_inputs.min(cand.len())).rev() {
            for combo in combinations(&cand, k) {
                let inset: HashSet<u32> = combo.iter().copied().collect();
                let cidx: Vec<usize> = idxs.iter().map(|&i| i as usize)
                    .filter(|&i| cls[i].iter().all(|l| l.unsigned_abs() == o || inset.contains(&l.unsigned_abs()))).collect();
                if cidx.is_empty() { continue; }
                let mut key: Vec<u32> = cidx.iter().map(|&i| i as u32).collect();
                key.sort_unstable();
                if !tried.insert(key) { continue; }
                // the inputs are the variables these clauses mention: a candidate none
                // of them mentions would be a dependency the gate does not have (and
                // can close a cycle through a gate downstream)
                let combo: Vec<u32> = combo.into_iter().filter(|&v| cidx.iter().any(|&i| cls[i].iter().any(|l| l.unsigned_abs() == v))).collect();
                let k = combo.len();
                // truth table over In (first input most significant)
                let mut table = Vec::with_capacity(1 << k);
                let mut ok = true;
                let pos: HashMap<u32, usize> = combo.iter().enumerate().map(|(j, &v)| (v, j)).collect();
                for row in 0..(1usize << k) {
                    let bit = |v: u32| -> bool { let j = pos[&v]; (row >> (k - 1 - j)) & 1 == 1 };
                    let mut allowed = [false, false];
                    for (ov, slot) in allowed.iter_mut().enumerate() {
                        let oval = ov == 1;
                        *slot = cidx.iter().all(|&i| cls[i].iter().any(|&l| {
                            let v = l.unsigned_abs();
                            let x = if v == o { oval } else { bit(v) };
                            (l > 0) == x
                        }));
                    }
                    if allowed[0] == allowed[1] { ok = false; break; }
                    table.push(allowed[1]);
                }
                if !ok { continue; }
                hit = Some((combo.clone(), cidx, table));
                break 'search;
            }
        }
        if let Some((ins, cidx, table)) = hit {
            for &i in &cidx { used[i] = true; }
            defined.insert(o);
            gates.push(Gate { out: o, inputs: ins.iter().map(|&v| v as i32).collect(), clauses: cidx, kind: Kind::Table(table) });
        }
    }
}

fn combinations(items: &[u32], k: usize) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    let n = items.len();
    if k > n { return out; }
    let mut idx: Vec<usize> = (0..k).collect();
    loop {
        out.push(idx.iter().map(|&i| items[i]).collect());
        let mut j = k;
        loop {
            if j == 0 { return out; }
            j -= 1;
            if idx[j] != j + n - k { break; }
            if j == 0 { return out; }
        }
        idx[j] += 1;
        for t in j + 1..k { idx[t] = idx[t - 1] + 1; }
    }
}

// ── the AIG ───────────────────────────────────────────────────────────────

struct Aig {
    ands: Vec<(u32, u32, u32)>,   // (lhs, rhs0, rhs1) AIGER literals, rhs0 >= rhs1, lhs > rhs0
    hash: HashMap<(u32, u32), u32>,
    next_var: u32,
}

impl Aig {
    fn new(ninputs: usize) -> Aig { Aig { ands: Vec::new(), hash: HashMap::new(), next_var: ninputs as u32 } }
    fn and(&mut self, a: u32, b: u32) -> u32 {
        if a == 0 || b == 0 { return 0; }
        if a == 1 { return b; }
        if b == 1 { return a; }
        if a == b { return a; }
        if a == b ^ 1 { return 0; }
        let (a, b) = if a < b { (b, a) } else { (a, b) };
        if let Some(&l) = self.hash.get(&(a, b)) { return l; }
        self.next_var += 1;
        let lhs = 2 * self.next_var;
        self.ands.push((lhs, a, b));
        self.hash.insert((a, b), lhs);
        lhs
    }
    fn and_list(&mut self, ls: &[u32]) -> u32 { let mut acc = 1; for &l in ls { acc = self.and(acc, l); } acc }
    fn or_list(&mut self, ls: &[u32]) -> u32 { let neg: Vec<u32> = ls.iter().map(|&l| l ^ 1).collect(); self.and_list(&neg) ^ 1 }
}

const NONE: u32 = u32::MAX;

/// The gates in topological order, and for every variable the gate that
/// defines it (NONE for an input).  A cycle of definitions is broken at one
/// of its gates: that gate is given up, its output is an input and its
/// clauses are plain clauses again; the gates that depend on it stay.
/// Depth first over the definitions: a gate met again while its own
/// definition is still being followed closes a cycle.
fn acyclic_order(gates: &[Gate], nv: usize) -> (Vec<u32>, Vec<u32>) {
    let mut gate_of: Vec<u32> = vec![NONE; nv + 1];
    for (gi, g) in gates.iter().enumerate() { if gate_of[g.out as usize] == NONE { gate_of[g.out as usize] = gi as u32; } }
    let mut state: Vec<u8> = vec![0; nv + 1];   // 0 new, 1 open, 2 closed
    let mut order: Vec<u32> = Vec::new();
    let mut stack: Vec<(u32, usize)> = Vec::new();
    for root in 1..=nv {
        if gate_of[root] == NONE || state[root] != 0 { continue; }
        state[root] = 1;
        stack.push((root as u32, 0));
        while let Some(top) = stack.last_mut() {
            let v = top.0 as usize;
            if gate_of[v] == NONE { state[v] = 2; stack.pop(); continue; }   // given up while open
            let ins = &gates[gate_of[v] as usize].inputs;
            if top.1 < ins.len() {
                let u = ins[top.1].unsigned_abs() as usize;
                top.1 += 1;
                if gate_of[u] == NONE { continue; }
                match state[u] {
                    0 => { state[u] = 1; stack.push((u as u32, 0)); }
                    1 => { gate_of[u] = NONE; }
                    _ => {}
                }
            } else {
                state[v] = 2;
                order.push(v as u32);
                stack.pop();
            }
        }
    }
    (order, gate_of)
}

/// The same gates level by level (a gate's level is one more than the
/// highest among its inputs): the first of a class of equal gates is then
/// one of the shallowest.
fn by_level(order: &mut [u32], gates: &[Gate], gate_of: &[u32]) {
    let mut level: Vec<u32> = vec![0; gate_of.len()];
    for &o in order.iter() {
        let g = &gates[gate_of[o as usize] as usize];
        level[o as usize] = 1 + g.inputs.iter().map(|l| level[l.unsigned_abs() as usize]).max().unwrap_or(0);
    }
    order.sort_by_key(|&o| level[o as usize]);
}

fn max_var(cls: &[Vec<i32>], gates: &[Gate]) -> usize {
    let a = cls.iter().flat_map(|c| c.iter()).map(|l| l.unsigned_abs()).max().unwrap_or(0);
    let b = gates.iter().map(|g| g.out).max().unwrap_or(0);
    a.max(b) as usize
}

struct Built {
    residual: Vec<usize>,
    pis: Vec<u32>,
    pos: Vec<u32>,
    aig: Aig,
    lit_of: HashMap<u32, u32>,
    ncyclic: usize,
    ngates: usize,
}

fn build_aig(cls: &[Vec<i32>], gates: &[Gate]) -> Built {
    let mut out_gate: HashMap<u32, usize> = HashMap::new();
    for (gi, g) in gates.iter().enumerate() { out_gate.entry(g.out).or_insert(gi); }
    let (order, _) = acyclic_order(gates, max_var(cls, gates));
    let kept: HashSet<u32> = order.iter().copied().collect();
    let ncyclic = out_gate.len() - kept.len();
    let mut defcl: Vec<bool> = vec![false; cls.len()];
    for &o in &kept { for &i in &gates[out_gate[&o]].clauses { defcl[i] = true; } }
    let residual: Vec<usize> = (0..cls.len()).filter(|&i| !defcl[i]).collect();
    let mut mentioned: HashSet<u32> = HashSet::new();
    for &i in &residual { for l in &cls[i] { mentioned.insert(l.unsigned_abs()); } }
    let mut pis: Vec<u32> = kept.iter().flat_map(|o| gates[out_gate[o]].inputs.iter().map(|l| l.unsigned_abs()))
        .filter(|v| !kept.contains(v)).collect::<HashSet<u32>>().into_iter().collect();
    pis.sort_unstable();
    let mut pos: Vec<u32> = kept.iter().copied().filter(|o| mentioned.contains(o)).collect();
    pos.sort_unstable();
    let mut aig = Aig::new(pis.len());
    let mut lit_of: HashMap<u32, u32> = HashMap::new();
    for (k, &v) in pis.iter().enumerate() { lit_of.insert(v, 2 * (k as u32 + 1)); }
    for &o in &order {
        let g = &gates[out_gate[&o]];
        let ins: Vec<u32> = g.inputs.iter().map(|&l| lit_of[&l.unsigned_abs()] ^ (l < 0) as u32).collect();
        let lit = match &g.kind {
            Kind::And { pos } => aig.and_list(&ins) ^ (!*pos) as u32,
            Kind::Table(t) => {
                let k = ins.len();
                let mut terms = Vec::new();
                for (row, &val) in t.iter().enumerate() {
                    if !val { continue; }
                    let ls: Vec<u32> = (0..k).map(|j| ins[j] ^ (((row >> (k - 1 - j)) & 1 == 0) as u32)).collect();
                    terms.push(aig.and_list(&ls));
                }
                if terms.is_empty() { 0 } else { aig.or_list(&terms) }
            }
        };
        lit_of.insert(o, lit);
    }
    Built { residual, pis, pos, aig, lit_of, ncyclic, ngates: out_gate.len() }
}

// ── proof-carrying re-encoding: hashing and dead cones, no ABC ────────────
//
// Output clauses are original clauses or RUP lemmas over the original
// variables; the DRAT prefix derives them and deletes the rest, so that the
// prefix followed by a solver's proof of the re-encoded formula refutes the
// original one.  Merged gates (same function of the same canonical inputs)
// are substituted away: the equivalence of two AND gates is RUP directly, a
// table gate's through a resolution tree over its inputs (2^(k+1)-1 lemmas,
// k <= 3).  A dead cone (no observed output depends on it) is deleted.

struct Proof { buf: Vec<u8>, lemmas: usize }
impl Proof {
    fn add(&mut self, c: &[i32]) { let mut l = String::new(); for x in c { let _ = write!(l, "{x} "); } l.push_str("0\n"); self.buf.extend_from_slice(l.as_bytes()); self.lemmas += 1; }
    fn del(&mut self, c: &[i32]) { let mut l = String::from("d "); for x in c { let _ = write!(l, "{x} "); } l.push_str("0\n"); self.buf.extend_from_slice(l.as_bytes()); }
}

/// Add `target` (a clause over the gate outputs and `vars`) by a resolution
/// tree over full assignments of `vars`: every leaf (not row, target) is RUP by
/// forward propagation through the gate definitions, every inner node from
/// its two children.  The intermediate lemmas are deleted again.
fn derive_by_rows(target: &[i32], vars: &[u32], proof: &mut Proof) {
    fn rec(target: &[i32], vars: &[u32], depth: usize, prefix: &mut Vec<i32>, proof: &mut Proof) {
        if depth == vars.len() {
            let mut c: Vec<i32> = prefix.iter().map(|&l| -l).collect(); c.extend_from_slice(target); proof.add(&c); return;
        }
        let v = vars[depth] as i32;
        for val in [-v, v] { prefix.push(val); rec(target, vars, depth + 1, prefix, proof); prefix.pop(); }
        let mut c: Vec<i32> = prefix.iter().map(|&l| -l).collect(); c.extend_from_slice(target); proof.add(&c);
        for val in [-v, v] { prefix.push(val); let mut d: Vec<i32> = prefix.iter().map(|&l| -l).collect(); d.extend_from_slice(target); proof.del(&d); prefix.pop(); }
    }
    let mut prefix = Vec::new();
    rec(target, vars, 0, &mut prefix, proof);
}

fn apply_rep(l: i32, rep: &[i32]) -> i32 { let r = rep[l.unsigned_abs() as usize]; if r == 0 { l } else if l > 0 { r } else { -r } }

/// Canonical key of a gate under the current substitution: None when the
/// canonical inputs collapse (a variable twice, or with its negation).
#[derive(Hash, PartialEq, Eq)]
enum Key { And(Vec<i32>), Table(Vec<u32>, Vec<bool>) }
fn canonical(g: &Gate, rep: &[i32]) -> Option<(Key, bool)> {
    match &g.kind {
        Kind::And { pos } => {
            let mut ins: Vec<i32> = g.inputs.iter().map(|&l| apply_rep(l, rep)).collect();
            ins.sort_unstable(); ins.dedup();
            for w in ins.windows(2) { if w[0] == -w[1] { return None; } }
            let vars: HashSet<u32> = ins.iter().map(|l| l.unsigned_abs()).collect();
            if vars.len() != ins.len() { return None; }
            Some((Key::And(ins), *pos))
        }
        Kind::Table(t) => {
            let k = g.inputs.len();
            let lits: Vec<i32> = g.inputs.iter().map(|&l| apply_rep(l, rep)).collect();
            let mut vars: Vec<u32> = lits.iter().map(|l| l.unsigned_abs()).collect();
            vars.sort_unstable();
            if vars.windows(2).any(|w| w[0] == w[1]) { return None; }
            // the table over the sorted canonical variables (first most significant)
            let pos_of: HashMap<u32, usize> = vars.iter().enumerate().map(|(j, &v)| (v, j)).collect();
            let mut nt = vec![false; 1 << k];
            for (row, slot) in nt.iter_mut().enumerate() {
                // original row bits: input i has canonical literal lits[i]; its value is the canonical var's bit, flipped if negated
                let mut orig = 0usize;
                for &l in lits.iter() {
                    let j = pos_of[&l.unsigned_abs()];
                    let bit = ((row >> (k - 1 - j)) & 1 == 1) != (l < 0);
                    orig = (orig << 1) | bit as usize;
                }
                *slot = t[orig];
            }
            let sign = nt[0];
            if sign { for b in nt.iter_mut() { *b = !*b; } }
            Some((Key::Table(vars, nt), !sign))
        }
    }
}

struct Recode { cls: Vec<Vec<i32>>, dropped: Vec<Vec<i32>>, merged: usize, dead: usize }

fn recode(cnf: &Cnf, root: &Root, gates: &[Gate], proof: &mut Proof) -> Recode {
    let nv = cnf.nv;
    let cls = &root.cls;
    // 1. root simplification: derived units and shortened clauses are RUP; the rest is deleted at the end
    for &u in &root.units { proof.add(&[u]); }
    let mut keep_original: Vec<bool> = vec![false; cnf.len()];      // input clauses that survive unchanged
    // 2. gates: topological order over the kept (acyclic) ones
    let mut out_gate: HashMap<u32, usize> = HashMap::new();
    for (gi, g) in gates.iter().enumerate() { out_gate.entry(g.out).or_insert(gi); }
    let (order, _) = acyclic_order(gates, nv);
    let kept: HashSet<u32> = order.iter().copied().collect();
    let mut defcl: Vec<bool> = vec![false; cls.len()];
    for &o in &kept { for &i in &gates[out_gate[&o]].clauses { defcl[i] = true; } }
    let residual: Vec<usize> = (0..cls.len()).filter(|&i| !defcl[i]).collect();
    // 3. hashing with substitution, in topological order
    let mut rep: Vec<i32> = vec![0; nv + 1];
    let mut table: HashMap<Key, (u32, bool)> = HashMap::new();
    let mut merged = 0usize;
    let mut live_gate: Vec<u32> = Vec::new();
    for &o in &order {
        let g = &gates[out_gate[&o]];
        match canonical(g, &rep) {
            None => { live_gate.push(o); }
            Some((key, sign)) => {
                if let Some(&(o1, sign1)) = table.get(&key) {
                    // o == o1 when the signs agree, else o == not o1
                    let neg = sign != sign1;
                    let e1 = if neg { -(o1 as i32) } else { o1 as i32 };
                    let o2 = o as i32;
                    match &g.kind {
                        Kind::And { .. } => { proof.add(&[-e1, o2]); proof.add(&[e1, -o2]); }
                        Kind::Table(_) => {
                            let vars: Vec<u32> = match &key { Key::Table(v, _) => v.clone(), _ => unreachable!() };
                            derive_by_rows(&[-e1, o2], &vars, proof);
                            derive_by_rows(&[e1, -o2], &vars, proof);
                        }
                    }
                    rep[o as usize] = e1; merged += 1;
                } else {
                    table.insert(key, (o, sign)); live_gate.push(o);
                }
            }
        }
    }
    // 4. dead cones: live = observed outputs and everything they depend on
    let mut mentioned: HashSet<u32> = HashSet::new();
    for &i in &residual { for &l in &cls[i] { mentioned.insert(apply_rep(l, &rep).unsigned_abs()); } }
    let mut needed: HashSet<u32> = HashSet::new();
    let mut stack: Vec<u32> = live_gate.iter().copied().filter(|o| mentioned.contains(o)).collect();
    while let Some(o) = stack.pop() {
        if !needed.insert(o) { continue; }
        for l in &gates[out_gate[&o]].inputs { let v = apply_rep(*l, &rep).unsigned_abs(); if kept.contains(&v) && rep[v as usize] == 0 { stack.push(v); } }
    }
    let dead = live_gate.iter().filter(|o| !needed.contains(o)).count();
    // 5. the output: substituted clauses of the needed gates and the residual, each an original or a RUP lemma
    let mut out: Vec<Vec<i32>> = Vec::new();
    let mut dropped: Vec<Vec<i32>> = Vec::new();
    let emit = |c: &Vec<i32>, orig: usize, out: &mut Vec<Vec<i32>>, proof: &mut Proof, keep_original: &mut Vec<bool>| {
        let mut nc: Vec<i32> = c.iter().map(|&l| apply_rep(l, &rep)).collect();
        if normalize(&mut nc) { return; }   // tautology after substitution
        let mut oc: Vec<i32> = cnf.clause(orig).to_vec(); normalize(&mut oc);
        if nc == oc { keep_original[orig] = true; out.push(cnf.clause(orig).to_vec()); return; }
        proof.add(&nc); out.push(nc);
    };
    for &o in &live_gate {
        let g = &gates[out_gate[&o]];
        if needed.contains(&o) { for &i in &g.clauses { emit(&cls[i], root.origin[i], &mut out, proof, &mut keep_original); } }
        else { for &i in &g.clauses { dropped.push(cls[i].clone()); } }
    }
    for &i in &residual { emit(&cls[i], root.origin[i], &mut out, proof, &mut keep_original); }
    for &u in &root.units { out.push(vec![u]); }
    // units that were original clauses stay; everything else original is deleted
    let unit_set: HashSet<i32> = root.units.iter().copied().collect();
    for (i, &kept_as_is) in keep_original.iter().enumerate() {
        let c = cnf.clause(i);
        if c.len() == 1 && unit_set.contains(&c[0]) { continue; }
        if !kept_as_is { proof.del(c); }
    }
    // the merge equivalences served their purpose
    for (v, &r) in rep.iter().enumerate() { if r != 0 { proof.del(&[-r, v as i32]); proof.del(&[r, -(v as i32)]); } }
    Recode { cls: out, dropped, merged, dead }
}

// ── certified SAT sweeping ────────────────────────────────────────────────
//
// Candidate equivalences come from random simulation of the gates.  Each is
// put to CaDiCaL on a window of the two cones: gates already merged are
// replaced by their representatives, and the window's boundary is left
// free, so an unsatisfiable answer holds for the whole circuit.  Two calls
// under assumptions, one per direction.  What the solver derives is implied
// by the window's clauses whatever the assumptions, and after an
// unsatisfiable call the clause of the negated assumptions follows by unit
// propagation: its learned clauses followed by that clause are a DRAT
// derivation of the equivalence from the gate definitions.  The checker
// holds the definitions in their original variables; propagating through
// the equivalences derived so far it follows every step the solver makes
// on the substituted ones, with one exception: where two literals of a
// clause have become one, the solver's clause is unit when the checker's
// still has two literals left.  Those shortened clauses are lemmas
// themselves, written when the gate is reached.  A satisfiable window that
// holds the whole cone is a real
// counterexample and refines the candidate classes; a satisfiable partial
// window decides nothing.  The ending is the re-encoding's: substituted
// clauses as lemmas, the replaced ones deleted.

struct SweepParams { rounds: usize, first_window: usize, max_window: usize, conflicts: i32, tries: usize, seconds: f64, recycle: usize, levels: bool, give_up: u32 }

#[derive(Default)]
struct SweepStats { attempts: usize, merged: usize, constants: usize, refuted: usize, window_sat: usize, unknown: usize, solver_lemmas: usize, splits: usize, shortened: usize, unreached: usize, given_up: usize, whole: usize, solvers: usize, clock: [f64; 4] }

/// The candidate classes: nodes (0 is the constant false, the others are
/// variables) that no pattern simulated so far tells apart, up to
/// complement.  A pattern that separates two of them splits their class.
struct Classes {
    id: Vec<u32>,
    members: Vec<Vec<u32>>,
    reps: Vec<Vec<u32>>,   // the settled representatives of a class, oldest first
    fails: Vec<u32>,       // attempts in a row that ran out of budget
}

impl Classes {
    /// Split by one more word of patterns; how many classes that made.
    fn refine(&mut self, word: &[u64]) -> usize {
        let n0 = self.members.len();
        let mut groups: HashMap<u64, u32> = HashMap::new();
        for c in 0..n0 {
            if self.members[c].len() < 2 { continue; }
            let w0 = word[self.members[c][0] as usize];
            if self.members[c].iter().all(|&v| word[v as usize] == w0) { continue; }
            groups.clear();
            groups.insert(w0, c as u32);
            let old = std::mem::take(&mut self.members[c]);
            for v in old {
                let w = word[v as usize];
                let t = match groups.get(&w) {
                    Some(&t) => t,
                    None => {
                        self.members.push(Vec::new()); self.reps.push(Vec::new());
                        let f = self.fails[c]; self.fails.push(f);
                        let t = (self.members.len() - 1) as u32; groups.insert(w, t); t
                    }
                };
                self.members[t as usize].push(v);
                self.id[v as usize] = t;
            }
            let old = std::mem::take(&mut self.reps[c]);
            for r in old { let t = self.id[r as usize] as usize; self.reps[t].push(r); }
        }
        self.members.len() - n0
    }
}

fn mix(k: u64, w: u64) -> u64 {
    let mut x = (k ^ w).wrapping_mul(0x9E37_79B9_7F4A_7C15);
    x ^= x >> 29;
    x = x.wrapping_mul(0xBF58_476D_1CE4_E5B9);
    x ^ (x >> 32)
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13; x ^= x >> 7; x ^= x << 17;
        self.0 = x;
        x.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }
}

/// A gate on 64 patterns at once.
fn eval_gate(g: &Gate, val: &[u64]) -> u64 {
    let lit = |l: i32| -> u64 { let w = val[l.unsigned_abs() as usize]; if l < 0 { !w } else { w } };
    match &g.kind {
        Kind::And { pos } => {
            let mut acc = !0u64;
            for &l in &g.inputs { acc &= lit(l); }
            if *pos { acc } else { !acc }
        }
        Kind::Table(t) => {
            let k = g.inputs.len();
            let mut out = 0u64;
            for (row, &on) in t.iter().enumerate() {
                if !on { continue; }
                let mut term = !0u64;
                for (j, &l) in g.inputs.iter().enumerate() {
                    let w = lit(l);
                    term &= if (row >> (k - 1 - j)) & 1 == 1 { w } else { !w };
                }
                out |= term;
            }
            out
        }
    }
}

enum Canon { Lit(i32), Const(bool) }

fn canon(l: i32, rep: &[i32], cval: &[i8]) -> Canon {
    let v = l.unsigned_abs() as usize;
    if cval[v] != 0 { let t = cval[v] > 0; return Canon::Const(if l > 0 { t } else { !t }); }
    let r = rep[v];
    Canon::Lit(if r == 0 { l } else if l > 0 { r } else { -r })
}

/// A clause as the solver sees it: representatives for merged variables,
/// constants evaluated; nothing when that satisfies it.  The flag: two of
/// its literals have become one.
fn substitute(c: &[i32], rep: &[i32], cval: &[i8]) -> Option<(Vec<i32>, bool)> {
    let mut nc: Vec<i32> = Vec::with_capacity(c.len());
    for &l in c {
        match canon(l, rep, cval) { Canon::Const(true) => return None, Canon::Const(false) => {}, Canon::Lit(x) => nc.push(x) }
    }
    let n = nc.len();
    if normalize(&mut nc) { return None; }
    let shortened = nc.len() < n;
    Some((nc, shortened))
}

enum Outcome {
    Proved,
    /// A counterexample over the circuit's inputs.
    Refuted(Vec<(u32, bool)>),
    WindowSat,
    Unknown,
}

fn drat_line(out: &mut Vec<u8>, delete: bool, c: &[i32]) {
    let mut line = String::with_capacity(8 * c.len() + 4);
    if delete { line.push_str("d "); }
    for x in c { let _ = write!(line, "{x} "); }
    line.push_str("0\n");
    out.extend_from_slice(line.as_bytes());
}

/// The variables one solver has seen, numbered in the order it saw them.
struct Numbering { id: Vec<i32>, stamp: Vec<u32>, generation: u32, vars: Vec<u32> }

impl Numbering {
    fn new(nv: usize) -> Numbering { Numbering { id: vec![0; nv + 1], stamp: vec![0; nv + 1], generation: 0, vars: Vec::new() } }
    fn local(&mut self, l: i32) -> i32 {
        let v = l.unsigned_abs() as usize;
        if self.stamp[v] != self.generation {
            self.stamp[v] = self.generation;
            self.vars.push(v as u32);
            self.id[v] = self.vars.len() as i32;
        }
        if l > 0 { self.id[v] } else { -self.id[v] }
    }
    fn global(&self, l: i32) -> i32 {
        let v = self.vars[l.unsigned_abs() as usize - 1] as i32;
        if l > 0 { v } else { -v }
    }
}

/// A CaDiCaL without preprocessing that records its proof, the gate
/// definitions it holds, and the lemmas of that proof the checker still
/// holds.
struct Session {
    solver: Solver,
    num: Numbering,
    live: HashMap<Vec<i32>, u32>,
    gates: usize,
    queries: usize,
}

impl Session {
    fn new(mut num: Numbering) -> Session {
        num.generation += 1;
        num.vars.clear();
        let mut solver: Solver = Solver::new();
        // no preprocessing: what the solver derives must follow from the clauses alone
        assert!(solver.configure("plain"), "CaDiCaL refused the plain configuration");
        assert!(solver.trace_proof_in_memory(), "CaDiCaL refused the proof tracer");
        Session { solver, num, live: HashMap::new(), gates: 0, queries: 0 }
    }

    /// The definition of a gate as it stands after the merges so far.
    fn load(&mut self, g: &Gate, cls: &[Vec<i32>], rep: &[i32], cval: &[i8]) -> bool {
        for &ci in &g.clauses {
            let Some((nc, _)) = substitute(&cls[ci], rep, cval) else { continue };
            if nc.is_empty() { return false; }
            let c: Vec<i32> = nc.iter().map(|&x| self.num.local(x)).collect();
            self.solver.add_clause(c.iter().copied());
        }
        self.gates += 1;
        true
    }

    fn ask(&mut self, assumptions: &[i32], budget: i32) -> Option<bool> {
        self.queries += 1;
        self.solver.limit("conflicts", budget);
        for &a in assumptions { let l = self.num.local(a); self.solver.assume(l); }
        self.solver.solve()
    }

    /// What the solver derived and deleted since the last time, as DRAT
    /// lines in the variables of the input; how many lemmas that is.
    fn drain(&mut self, out: &mut Vec<u8>) -> usize {
        assert!(!self.solver.proof_has_rat(), "CaDiCaL derived a clause that is not implied");
        let ev = self.solver.proof_events();
        let mut lemmas = 0usize;
        let mut i = 0;
        while i < ev.len() {
            let tag = ev[i]; i += 1;
            let mut c: Vec<i32> = Vec::new();
            while ev[i] != 0 { c.push(self.num.global(ev[i])); i += 1; }
            i += 1;
            drat_line(out, tag != 1, &c);
            c.sort_unstable();
            if tag == 1 {
                lemmas += 1;
                *self.live.entry(c).or_insert(0) += 1;
            } else if let Some(n) = self.live.get_mut(&c) {
                *n -= 1;
                if *n == 0 { self.live.remove(&c); }
            }
        }
        self.solver.proof_events_clear();
        lemmas
    }

    /// The solver goes, and with it the lemmas the checker still holds.
    fn retire(mut self, out: &mut Vec<u8>) -> (usize, Numbering) {
        let lemmas = self.drain(out);
        let mut rest: Vec<(&Vec<i32>, &u32)> = self.live.iter().collect();
        rest.sort();
        for (c, &n) in rest { for _ in 0..n { drat_line(out, true, c); } }
        (lemmas, self.num)
    }

    /// The values of the circuit's inputs in the model.
    fn inputs(&self, gate_of: &[u32]) -> Vec<(u32, bool)> {
        self.num.vars.iter().enumerate().filter(|(_, v)| gate_of[**v as usize] == NONE)
            .map(|(k, &v)| (v, self.solver.value(k as i32 + 1) == Some(true))).collect()
    }
}

struct Sweeper<'a> {
    cls: &'a [Vec<i32>],
    gates: &'a [Gate],
    gate_of: Vec<u32>,
    rep: Vec<i32>,
    cval: Vec<i8>,
    seen: Vec<u32>,
    stamp: u32,
    spare: Option<Numbering>,      // of the solver for windows, between two of them
    cones: Option<Session>,        // the solver for whole cones
    rested: Option<Numbering>,     // its numbering, between two of them
    loaded: Vec<u32>,              // gate -> the whole-cone solver that holds it (by the generation of its numbering)
    whole: usize,
    solvers: usize,
    last_cone: usize,              // gates put to the solver in the last attempt
    clock: [f64; 4],               // seconds: windows, loading whole cones, solving on them, simulation
    p: &'a SweepParams,
}

impl Sweeper<'_> {
    /// The gates whose definitions are loaded, breadth first from the pair,
    /// and whether that is every gate below it.
    fn window(&mut self, o: u32, r: u32, limit: usize) -> (Vec<u32>, bool) {
        self.stamp += 1;
        let s = self.stamp;
        let mut q: Vec<u32> = vec![o];
        self.seen[o as usize] = s;
        if r != 0 && self.gate_of[r as usize] != NONE && self.seen[r as usize] != s { self.seen[r as usize] = s; q.push(r); }
        let mut i = 0;
        while i < q.len() && i < limit {
            let g = &self.gates[self.gate_of[q[i] as usize] as usize];
            i += 1;
            for &l in &g.inputs {
                if let Canon::Lit(c) = canon(l, &self.rep, &self.cval) {
                    let u = c.unsigned_abs() as usize;
                    if self.gate_of[u] != NONE && self.seen[u] != s { self.seen[u] = s; q.push(u as u32); }
                }
            }
        }
        let complete = i >= q.len();
        q.truncate(i);
        (q, complete)
    }

    /// The whole-cone solver goes; its lemmas leave the proof.
    fn rest(&mut self, proof: &mut Proof) {
        if let Some(s) = self.cones.take() {
            let (lemmas, num) = s.retire(&mut proof.buf);
            proof.lemmas += lemmas;
            self.rested = Some(num);
        }
    }

    /// o == r (or not r when `neg`); r = 0 is the constant false.  A proof
    /// goes to `proof`: what the solver derived, then the clause of the
    /// negated assumptions, once per direction.
    fn prove(&mut self, o: u32, r: u32, neg: bool, proof: &mut Proof) -> Outcome {
        let lo = o as i32;
        let lr = if neg { -(r as i32) } else { r as i32 };
        // to refute: o without r, r without o; for the constant, the value o does not take
        let calls: Vec<Vec<i32>> = if r == 0 { vec![vec![if neg { -lo } else { lo }]] } else { vec![vec![lo, -lr], vec![-lo, lr]] };
        let negated = |a: &Vec<i32>| -> Vec<i32> { a.iter().map(|&x| -x).collect() };

        // 1. a window below the pair, in a solver of its own: what it proves
        // holds whatever is below the window
        let t = std::time::Instant::now();
        let (wg, complete) = self.window(o, r, self.p.first_window);
        self.last_cone = wg.len();
        let mut s = Session::new(self.spare.take().expect("the numbering of the window solver"));
        let mut sound = true;
        for &g in &wg { sound &= s.load(&self.gates[self.gate_of[g as usize] as usize], self.cls, &self.rep, &self.cval); }
        let mut lines: Vec<u8> = Vec::new();
        let mut lemmas = 0usize;
        let mut verdict = if sound { Some(false) } else { None };
        if sound {
            for a in &calls {
                verdict = s.ask(a, self.p.conflicts);
                if verdict != Some(false) { break; }
                lemmas += s.drain(&mut lines);
                drat_line(&mut lines, false, &negated(a));
                lemmas += 1;
            }
        }
        let first = match verdict {
            Some(false) => Outcome::Proved,
            Some(true) if complete => Outcome::Refuted(s.inputs(&self.gate_of)),
            Some(true) => Outcome::WindowSat,
            None => Outcome::Unknown,
        };
        let (more, num) = s.retire(&mut lines);
        self.spare = Some(num);
        self.clock[0] += t.elapsed().as_secs_f64();
        match first {
            Outcome::Proved => { proof.buf.extend_from_slice(&lines); proof.lemmas += lemmas + more; return Outcome::Proved; }
            Outcome::Refuted(_) => return first,
            _ => if !sound || self.p.max_window <= self.p.first_window { return first; }
        }

        // 2. the whole cones, in the solver that holds the cones of the gates
        // before -- unless it holds much else: a call costs what the solver
        // holds, not what the question is about
        let t = std::time::Instant::now();
        let (cone, _) = self.window(o, r, usize::MAX);
        self.last_cone = cone.len();
        if cone.len() > self.p.max_window { return Outcome::WindowSat; }
        if let Some(s) = &self.cones
            && (s.gates > 2 * cone.len() + 1000 || s.queries >= self.p.recycle) { self.rest(proof); }
        if self.cones.is_none() {
            self.cones = Some(Session::new(self.rested.take().expect("the numbering of the whole-cone solver")));
            self.solvers += 1;
        }
        let s = self.cones.as_mut().unwrap();
        let generation = s.num.generation;
        for &g in &cone {
            if self.loaded[g as usize] == generation { continue; }
            if !s.load(&self.gates[self.gate_of[g as usize] as usize], self.cls, &self.rep, &self.cval) { return Outcome::Unknown; }
            self.loaded[g as usize] = generation;
        }
        self.whole += 1;
        self.clock[1] += t.elapsed().as_secs_f64();
        let t = std::time::Instant::now();
        // a conflict costs what the cone weighs: the budget is for a cone of 4096 gates
        let budget = ((self.p.conflicts as u64 * 4096 / cone.len().max(4096) as u64) as i32).max(20).min(self.p.conflicts);
        let mut done: Vec<Vec<i32>> = Vec::new();
        let mut verdict = Some(false);
        for a in &calls {
            verdict = s.ask(a, budget);
            proof.lemmas += s.drain(&mut proof.buf);    // whatever the answer: the solver keeps what it learned
            if verdict != Some(false) { break; }
            let c = negated(a);
            drat_line(&mut proof.buf, false, &c);
            proof.lemmas += 1;
            done.push(c);
        }
        self.clock[2] += t.elapsed().as_secs_f64();
        match verdict {
            Some(false) => Outcome::Proved,
            other => {
                for c in &done { drat_line(&mut proof.buf, true, c); }   // one direction alone is of no use
                if other == Some(true) { Outcome::Refuted(s.inputs(&self.gate_of)) } else { Outcome::Unknown }
            }
        }
    }
}

fn sweep(cnf: &Cnf, root: &Root, gates: &[Gate], p: &SweepParams, proof: &mut Proof, t0: std::time::Instant) -> (Recode, SweepStats) {
    let nv = cnf.nv;
    let cls = &root.cls;
    for &u in &root.units { proof.add(&[u]); }
    // the gates in topological order; one given up to break a cycle is an input here
    let (mut order, gate_of) = acyclic_order(gates, nv);
    if p.levels { by_level(&mut order, gates, &gate_of); }
    let mut defcl: Vec<bool> = vec![false; cls.len()];
    for &o in &order { for &i in &gates[gate_of[o as usize] as usize].clauses { defcl[i] = true; } }
    let residual: Vec<usize> = (0..cls.len()).filter(|&i| !defcl[i]).collect();
    let mut is_input: Vec<bool> = vec![false; nv + 1];
    for &o in &order { for l in &gates[gate_of[o as usize] as usize].inputs { let u = l.unsigned_abs() as usize; if gate_of[u] == NONE { is_input[u] = true; } } }

    // candidate classes by simulation.  A node's patterns are complemented
    // when its first one is 1, so that a node and its complement agree.
    let mut rng = Rng(0x9E37_79B9_7F4A_7C15);
    let mut key: Vec<u64> = vec![0; nv + 1];
    let mut phase: Vec<bool> = vec![false; nv + 1];
    let mut val: Vec<u64> = vec![0; nv + 1];
    let in_circuit = |v: usize| v == 0 || is_input[v] || gate_of[v] != NONE;
    for round in 0..p.rounds.max(1) {
        for v in 1..=nv { if gate_of[v] == NONE { val[v] = rng.next(); } }
        for &o in &order { val[o as usize] = eval_gate(&gates[gate_of[o as usize] as usize], &val); }
        for v in 1..=nv {
            if round == 0 { phase[v] = val[v] & 1 == 1; }
            key[v] = mix(key[v], if phase[v] { !val[v] } else { val[v] });
        }
        key[0] = mix(key[0], 0);
    }
    let mut classes = Classes { id: vec![NONE; nv + 1], members: Vec::new(), reps: Vec::new(), fails: Vec::new() };
    {
        let mut by_key: HashMap<u64, u32> = HashMap::new();
        for v in (0..=nv).filter(|&v| in_circuit(v)) {
            let c = *by_key.entry(key[v]).or_insert_with(|| { classes.members.push(Vec::new()); classes.reps.push(Vec::new()); classes.fails.push(0); (classes.members.len() - 1) as u32 });
            classes.members[c as usize].push(v as u32);
            classes.id[v] = c;
        }
        // the constant and the inputs are settled from the start
        for v in (0..=nv).filter(|&v| v == 0 || is_input[v]) { classes.reps[classes.id[v] as usize].push(v as u32); }
    }
    drop(key);

    let mut sw = Sweeper { cls, gates, gate_of, rep: vec![0; nv + 1], cval: vec![0; nv + 1], seen: vec![0; nv + 1], stamp: 0,
                           spare: Some(Numbering::new(nv)), cones: None, rested: Some(Numbering::new(nv)), loaded: vec![0; nv + 1],
                           whole: 0, solvers: 0, last_cone: 0, clock: [0.0; 4], p };
    let mut st = SweepStats::default();
    let mut const_units: Vec<i32> = Vec::new();
    let mut shortened: HashMap<usize, Vec<i32>> = HashMap::new();
    let mut in_model: Vec<u32> = vec![0; nv + 1];
    let mut model_stamp = 0u32;
    // SWEEP_TRACE=file: one line per attempt (position, gate, candidate, outcome, gates in the cone, size of the class)
    let mut trace = std::env::var("SWEEP_TRACE").ok().map(|f| std::io::BufWriter::new(std::fs::File::create(f).expect("SWEEP_TRACE")));
    let started = std::time::Instant::now();
    let mut last = std::time::Instant::now();
    for (n, &o) in order.iter().enumerate() {
        let ou = o as usize;
        // the inputs of this gate are settled: where two literals of a clause
        // have become one the shorter clause is a lemma, and what is derived
        // from here on may lean on it
        for &ci in &gates[sw.gate_of[ou] as usize].clauses {
            if let Some((nc, true)) = substitute(&cls[ci], &sw.rep, &sw.cval) { proof.add(&nc); shortened.insert(ci, nc); st.shortened += 1; }
        }
        let out_of_time = p.seconds > 0.0 && started.elapsed().as_secs_f64() > p.seconds;
        if out_of_time && !classes.reps[classes.id[ou] as usize].is_empty() { st.unreached += 1; }
        let mut tried: Vec<u32> = Vec::new();
        let mut undecided = 0usize;
        let mut done = false;
        while !out_of_time && undecided < p.tries && tried.len() < p.tries + 8 {
            // the oldest representative the patterns cannot tell from this gate
            let c = classes.id[ou] as usize;
            if classes.fails[c] >= p.give_up { if !classes.reps[c].is_empty() { st.given_up += 1; } break; }
            let Some(r) = classes.reps[c].iter().copied().find(|r| !tried.contains(r)) else { break };
            tried.push(r);
            st.attempts += 1;
            let neg = phase[ou] != (r != 0 && phase[r as usize]);
            let outcome = sw.prove(o, r, neg, proof);
            if let Some(f) = trace.as_mut() {
                let what = match &outcome { Outcome::Proved => "proved", Outcome::Refuted(_) => "refuted", Outcome::WindowSat => "window", Outcome::Unknown => "budget" };
                let _ = writeln!(f, "{n} {o} {r} {what} {} {}", sw.last_cone, classes.members[classes.id[ou] as usize].len());
            }
            match outcome {
                Outcome::Proved => {
                    classes.fails[c] = 0;
                    if r == 0 {
                        sw.cval[ou] = if neg { 1 } else { -1 };
                        const_units.push(if neg { o as i32 } else { -(o as i32) });
                        st.constants += 1;
                    } else {
                        sw.rep[ou] = if neg { -(r as i32) } else { r as i32 };
                        st.merged += 1;
                    }
                    done = true;
                    break;
                }
                Outcome::Refuted(model) => {
                    // the counterexample and 63 patterns near it, through the whole circuit
                    let t = std::time::Instant::now();
                    st.refuted += 1;
                    model_stamp += 1;
                    for &(v, b) in &model {
                        in_model[v as usize] = model_stamp;
                        let flips = rng.next() & rng.next() & rng.next() & !1;
                        val[v as usize] = (if b { !0u64 } else { 0 }) ^ flips;
                    }
                    for v in 1..=nv { if sw.gate_of[v] == NONE && in_model[v] != model_stamp { val[v] = rng.next(); } }
                    for &g in &order { val[g as usize] = eval_gate(&gates[sw.gate_of[g as usize] as usize], &val); }
                    for v in 1..=nv { if phase[v] { val[v] = !val[v]; } }
                    val[0] = 0;
                    st.splits += classes.refine(&val);
                    sw.clock[3] += t.elapsed().as_secs_f64();
                }
                Outcome::WindowSat => { st.window_sat += 1; undecided += 1; classes.fails[c] += 1; }
                Outcome::Unknown => { st.unknown += 1; undecided += 1; classes.fails[c] += 1; }
            }
        }
        if !done { let c = classes.id[ou] as usize; classes.reps[c].push(o); }
        if last.elapsed().as_secs() >= 30 {
            last = std::time::Instant::now();
            println!("  sweep: {}/{} gates, {} attempts: {} merged, {} constant, {} refuted, {} undecided ({:.0}s: windows {:.0}, loading {:.0}, whole cones {:.0} ({} calls, {} gates held), simulation {:.0})",
                     n + 1, order.len(), st.attempts, st.merged, st.constants, st.refuted, st.window_sat + st.unknown, t0.elapsed().as_secs_f64(),
                     sw.clock[0], sw.clock[1], sw.clock[2], sw.whole, sw.cones.as_ref().map(|s| s.gates).unwrap_or(0), sw.clock[3]);
        }
    }

    sw.rest(proof);
    if let Ok(f) = std::env::var("SWEEP_REPS") {
        // what was merged: a variable and the literal it equals, or its value
        let mut t = String::new();
        for v in 1..=nv {
            if sw.cval[v] != 0 { let _ = writeln!(t, "{v} = {}", if sw.cval[v] > 0 { "true" } else { "false" }); }
            else if sw.rep[v] != 0 { let _ = writeln!(t, "{v} = {}", sw.rep[v]); }
        }
        std::fs::write(f, t).expect("SWEEP_REPS");
    }
    st.whole = sw.whole;
    st.solvers = sw.solvers;
    st.clock = sw.clock;
    st.solver_lemmas = proof.lemmas - root.units.len() - st.shortened - 2 * st.merged - st.constants;

    // the output: what the observed outputs depend on, substituted
    let (rep, cval, gate_of) = (sw.rep, sw.cval, sw.gate_of);
    let is_rep_gate = |v: usize| gate_of[v] != NONE && rep[v] == 0 && cval[v] == 0;
    let mut needed: Vec<bool> = vec![false; nv + 1];
    let mut stack: Vec<u32> = Vec::new();
    for &i in &residual { for &l in &cls[i] { if let Canon::Lit(c) = canon(l, &rep, &cval) { let u = c.unsigned_abs() as usize; if is_rep_gate(u) { stack.push(u as u32); } } } }
    while let Some(o) = stack.pop() {
        if needed[o as usize] { continue; }
        needed[o as usize] = true;
        for &l in &gates[gate_of[o as usize] as usize].inputs {
            if let Canon::Lit(c) = canon(l, &rep, &cval) { let u = c.unsigned_abs() as usize; if is_rep_gate(u) && !needed[u] { stack.push(u as u32); } }
        }
    }
    let mut keep_original: Vec<bool> = vec![false; cnf.len()];
    let mut out: Vec<Vec<i32>> = Vec::new();
    let mut dropped: Vec<Vec<i32>> = Vec::new();
    let mut dead = 0usize;
    let mut emit = |i: usize, out: &mut Vec<Vec<i32>>, proof: &mut Proof| {
        let Some((nc, _)) = substitute(&cls[i], &rep, &cval) else { return };
        let orig = root.origin[i];
        let mut oc: Vec<i32> = cnf.clause(orig).to_vec(); normalize(&mut oc);
        if nc == oc { keep_original[orig] = true; out.push(cnf.clause(orig).to_vec()); return; }
        if !shortened.contains_key(&i) { proof.add(&nc); }   // the empty clause, if the circuit contradicts the rest
        out.push(nc);
    };
    let mut spent: Vec<usize> = Vec::new();
    for &o in &order {
        let ou = o as usize;
        let g = &gates[gate_of[ou] as usize];
        if is_rep_gate(ou) && needed[ou] { for &i in &g.clauses { emit(i, &mut out, proof); } continue; }
        // merged, constant or unobserved: the definition goes, and a model of
        // the output extends through it
        if is_rep_gate(ou) { dead += 1; }
        for &i in &g.clauses { dropped.push(cls[i].clone()); if shortened.contains_key(&i) { spent.push(i); } }
    }
    for &i in &residual { emit(i, &mut out, proof); }
    for &u in &root.units { out.push(vec![u]); }
    for &u in &const_units { out.push(vec![u]); }
    let unit_set: HashSet<i32> = root.units.iter().copied().collect();
    for (i, &kept_as_is) in keep_original.iter().enumerate() {
        let c = cnf.clause(i);
        if c.len() == 1 && unit_set.contains(&c[0]) { continue; }
        if !kept_as_is { proof.del(c); }
    }
    for (v, &r) in rep.iter().enumerate() { if r != 0 { proof.del(&[-r, v as i32]); proof.del(&[r, -(v as i32)]); } }
    for i in spent { proof.del(&shortened[&i]); }
    (Recode { cls: out, dropped, merged: st.merged + st.constants, dead }, st)
}

fn enc7(mut x: u32, out: &mut Vec<u8>) {
    loop { let b = (x & 0x7f) as u8; x >>= 7; if x != 0 { out.push(b | 0x80); } else { out.push(b); return; } }
}

fn write_aig(path: &str, b: &Built) -> Result<(), String> {
    let i = b.pis.len();
    let a = b.aig.ands.len();
    let mut out: Vec<u8> = Vec::with_capacity(a * 4 + 64);
    out.extend_from_slice(format!("aig {} {} 0 {} {}\n", i + a, i, b.pos.len(), a).as_bytes());
    for o in &b.pos { out.extend_from_slice(format!("{}\n", b.lit_of[o]).as_bytes()); }
    for (n, &(lhs, r0, r1)) in b.aig.ands.iter().enumerate() {
        debug_assert!(lhs == 2 * (i as u32 + n as u32 + 1) && r0 >= r1 && lhs > r0);
        enc7(lhs - r0, &mut out);
        enc7(r0 - r1, &mut out);
    }
    std::fs::write(path, out).map_err(|e| e.to_string())
}

/// Binary or ascii AIGER: (I, O, A, outputs).
fn read_aiger(path: &str) -> Result<(usize, usize, usize, Vec<u32>), String> {
    let data = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let nl = data.iter().position(|&b| b == b'\n').ok_or("no header")?;
    let head = std::str::from_utf8(&data[..nl]).map_err(|e| e.to_string())?;
    let f: Vec<&str> = head.split_whitespace().collect();
    if f.len() < 6 { return Err("short header".into()); }
    let (i, l, o, a): (usize, usize, usize, usize) = (f[2].parse().unwrap(), f[3].parse().unwrap(), f[4].parse().unwrap(), f[5].parse().unwrap());
    if l != 0 { return Err("latches".into()); }
    let mut pos = nl + 1;
    let mut outputs = Vec::with_capacity(o);
    if f[0] == "aig" {
        for _ in 0..o {
            let e = data[pos..].iter().position(|&b| b == b'\n').map(|p| pos + p).ok_or("truncated")?;
            outputs.push(std::str::from_utf8(&data[pos..e]).unwrap().trim().parse::<u32>().map_err(|e| e.to_string())?);
            pos = e + 1;
        }
        Ok((i, o, a, outputs))
    } else {
        let text = std::str::from_utf8(&data[pos..]).map_err(|e| e.to_string())?;
        let lines: Vec<&str> = text.lines().collect();
        for k in 0..o { outputs.push(lines[i + k].trim().parse::<u32>().map_err(|e| e.to_string())?); }
        Ok((i, o, a, outputs))
    }
}

// ── the ABC back-end ──────────────────────────────────────────────────────

fn script_for(name: &str) -> &str {
    match name {
        "none" => "",
        "resyn2" => "balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance",
        "resyn2f" => "balance; rewrite; refactor; balance; rewrite; rewrite -z; balance; refactor -z; rewrite -z; balance; fraig",
        "dc2" => "dc2",
        "dc2f" => "dc2; fraig; dc2",
        "compress2" => "balance -l; rewrite -l; refactor -l; balance -l; rewrite -l; rewrite -zl; balance -l; refactor -zl; rewrite -zl; balance -l",
        other => other,
    }
}

/// ABC's `&write_cnf -i -o`: CNF variable = GIA object id + 1 (constant 0,
/// inputs 1..I, ands, outputs I+A+1..); no clause asserts the outputs; ids
/// the cut mapping left unused are forced false.  Inputs and outputs take
/// the original variables, every other id a fresh one; a unit on an input id
/// is the writer's don't-care and is dropped.
fn abc_cnf_to_cnf(nv: usize, path: &str, pis: &[u32], pos: &[u32], gi: usize, ga: usize) -> Result<(usize, Vec<Vec<i32>>), String> {
    let bytes = std::fs::read(path).map_err(|e| format!("{path}: {e}"))?;
    let raw = parse_dimacs(&bytes)?;
    let mut rename: HashMap<u32, u32> = HashMap::new();
    for (k, &v) in pis.iter().enumerate() { rename.insert(k as u32 + 2, v); }
    for (j, &o) in pos.iter().enumerate() { rename.insert((gi + ga + 2 + j) as u32, o); }
    let pi_ids: HashSet<u32> = (2..(gi as u32 + 2)).collect();
    let mut next = nv as u32;
    let mut out: Vec<Vec<i32>> = Vec::with_capacity(raw.len());
    for i in 0..raw.len() {
        let c = raw.clause(i);
        if c.is_empty() { continue; }
        if c.len() == 1 && pi_ids.contains(&c[0].unsigned_abs()) { continue; }
        let mut nc = Vec::with_capacity(c.len());
        for &l in c {
            let x = l.unsigned_abs();
            let v = *rename.entry(x).or_insert_with(|| { next += 1; next });
            nc.push(if l < 0 { -(v as i32) } else { v as i32 });
        }
        out.push(nc);
    }
    Ok((next as usize, out))
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 { eprintln!("usage: cnf2aig in.cnf [--out out.cnf] [--abc ABC] [--script S] [--aag file.aig] [--keep dir]"); std::process::exit(2); }
    let mut input = None; let mut out = None; let mut abc = None; let mut script = "resyn2".to_string(); let mut aag = None; let mut keep = None;
    let mut recode_out = None; let mut proof_out = None; let mut dropped_out = None; let mut sweep_out = None; let mut map_out: Option<String> = None;
    let mut sp = SweepParams { rounds: 16, first_window: 64, max_window: usize::MAX, conflicts: 1000, tries: 2, seconds: 0.0, recycle: 1000, levels: true, give_up: 32 };
    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--out" => { out = Some(args[i + 1].clone()); i += 2; }
            "--abc" => { abc = Some(args[i + 1].clone()); i += 2; }
            "--script" => { script = args[i + 1].clone(); i += 2; }
            "--aag" => { aag = Some(args[i + 1].clone()); i += 2; }
            "--keep" => { keep = Some(args[i + 1].clone()); i += 2; }
            "--recode" => { recode_out = Some(args[i + 1].clone()); i += 2; }
            "--proof" => { proof_out = Some(args[i + 1].clone()); i += 2; }
            "--dropped" => { dropped_out = Some(args[i + 1].clone()); i += 2; }
            "--sweep" => { sweep_out = Some(args[i + 1].clone()); i += 2; }
            "--map" => { map_out = Some(args[i + 1].clone()); i += 2; }
            "--rounds" => { sp.rounds = args[i + 1].parse().expect("--rounds N"); i += 2; }
            "--window" => { sp.max_window = args[i + 1].parse().expect("--window N"); i += 2; }
            "--conflicts" => { sp.conflicts = args[i + 1].parse().expect("--conflicts N"); i += 2; }
            "--tries" => { sp.tries = args[i + 1].parse().expect("--tries N"); i += 2; }
            "--seconds" => { sp.seconds = args[i + 1].parse().expect("--seconds S"); i += 2; }
            "--first" => { sp.first_window = args[i + 1].parse().expect("--first N"); i += 2; }
            "--give-up" => { sp.give_up = args[i + 1].parse::<u32>().expect("--give-up N").max(1); i += 2; }
            "--order" => { sp.levels = match args[i + 1].as_str() { "level" => true, "depth" => false, _ => { eprintln!("--order level|depth"); std::process::exit(2) } }; i += 2; }
            "--recycle" => { sp.recycle = args[i + 1].parse::<usize>().expect("--recycle N").max(2); i += 2; }
            s if s.starts_with("--") => { eprintln!("unknown option {s}"); std::process::exit(2); }
            _ => { input = Some(args[i].clone()); i += 1; }
        }
    }
    sp.first_window = sp.first_window.min(sp.max_window).max(1);
    sp.max_window = sp.max_window.max(1);
    let input = input.expect("input CNF");
    let base = std::path::Path::new(&input).file_name().unwrap().to_string_lossy().to_string();
    let t0 = std::time::Instant::now();
    let bytes = std::fs::read(&input).unwrap_or_else(|e| { eprintln!("{input}: {e}"); std::process::exit(2) });
    let cnf = parse_dimacs(&bytes).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(2) });
    let nv = cnf.nv;
    let root = simplify_root(&cnf);
    if root.unsat {
        println!("{base}: the unit clauses contradict -- writing the empty clause");
        if let Some(o) = out.clone().or(recode_out.clone()).or(sweep_out.clone()) { write_cnf(&o, nv, &[vec![]]).unwrap(); }
        if let Some(p) = proof_out { std::fs::write(p, "0\n").unwrap(); }  // the empty clause is RUP from the contradicting units
        return;
    }
    let cls = root.cls.clone();
    println!("{base}: root simplification: {} units, {} -> {} clauses ({:.1}s)", root.units.len(), cnf.len(), cls.len(), t0.elapsed().as_secs_f64());
    // both orientations of the symmetric groups; keep the one with fewer cycles
    let mut best: Option<(usize, &str, Built)> = None;
    for (name, xor) in [("highest-variable", true), ("fewest-occurrences", false)] {
        let mut gates = extract_pattern(&cls, xor);
        let np = gates.len();
        extract_generic(&cls, &mut gates, 3);
        let built = build_aig(&cls, &gates);
        println!("  orientation {name}: {np} by pattern + {} generic, {} given up to break cycles ({:.1}s)", gates.len() - np, built.ncyclic, t0.elapsed().as_secs_f64());
        let kept = built.ngates - built.ncyclic;
        if best.as_ref().map(|b| kept > b.0).unwrap_or(true) { best = Some((kept, name, built)); }
        if best.as_ref().map(|b| b.2.ncyclic == 0).unwrap_or(false) { break; }
    }
    let (_, name, b) = best.unwrap();
    println!("  orientation kept: {name}");
    if let Some(wp) = &sweep_out {
        let mut gates = extract_pattern(&cls, name == "highest-variable");
        extract_generic(&cls, &mut gates, 3);
        let mut proof = Proof { buf: Vec::new(), lemmas: 0 };
        let (r, st) = sweep(&cnf, &root, &gates, &sp, &mut proof, t0);
        write_cnf(wp, nv, &r.cls).unwrap();
        if let Some(pp) = &proof_out { std::fs::write(pp, &proof.buf).unwrap(); }
        if let Some(dp) = &dropped_out { write_cnf(dp, nv, &r.dropped).unwrap(); }
        println!("{base}: sweep: {} attempts: {} merged, {} constant, {} refuted ({} refinements), {} undecided in the window, {} out of budget; {} dead; {} candidates not reached in time, {} in classes given up",
                 st.attempts, st.merged, st.constants, st.refuted, st.splits, st.window_sat, st.unknown, r.dead, st.unreached, st.given_up);
        println!("{base}: sweep: {} of the attempts went to whole cones, in {} solvers; seconds: windows {:.1}, loading {:.1}, whole cones {:.1}, simulation {:.1}",
                 st.whole, st.solvers, st.clock[0], st.clock[1], st.clock[2], st.clock[3]);
        println!("{base}: sweep: {} -> {} clauses, {} proof lemmas ({} from the solver, {} shortened clauses), {:.1} MB of proof ({:.1}s)",
                 cnf.len(), r.cls.len(), proof.lemmas, st.solver_lemmas, st.shortened, proof.buf.len() as f64 / 1e6, t0.elapsed().as_secs_f64());
        if out.is_none() && recode_out.is_none() { return; }
    }
    if let Some(rp) = &recode_out {
        // the gates of the kept orientation, extracted again (cheap)
        let mut gates = extract_pattern(&cls, name == "highest-variable");
        extract_generic(&cls, &mut gates, 3);
        let mut proof = Proof { buf: Vec::new(), lemmas: 0 };
        let r = recode(&cnf, &root, &gates, &mut proof);
        write_cnf(rp, nv, &r.cls).unwrap();
        if let Some(pp) = &proof_out { std::fs::write(pp, &proof.buf).unwrap(); }
        if let Some(dp) = &dropped_out { write_cnf(dp, nv, &r.dropped).unwrap(); }
        println!("{base}: recode: {} gates merged, {} dead, {} -> {} clauses, {} proof lemmas ({:.1}s)", r.merged, r.dead, cnf.len(), r.cls.len(), proof.lemmas, t0.elapsed().as_secs_f64());
        if out.is_none() { return; }
    }
    println!("{base}: {nv} vars, {} clauses; {} gates ({} given up to break cycles), AIG {} inputs, {} outputs, {} ands; residual {} clauses ({:.1}s)",
             cls.len(), b.ngates, b.ncyclic, b.pis.len(), b.pos.len(), b.aig.ands.len(), b.residual.len(), t0.elapsed().as_secs_f64());
    let units: Vec<Vec<i32>> = root.units.iter().map(|&l| vec![l]).collect();
    if let Some(p) = &aag { write_aig(p, &b).unwrap(); }
    if let Some(p) = &map_out {
        // the variable of every input and output of the AIG, in its order
        let mut t = String::new();
        for (k, v) in b.pis.iter().enumerate() { let _ = writeln!(t, "i {k} {v}"); }
        for (k, v) in b.pos.iter().enumerate() { let _ = writeln!(t, "o {k} {v}"); }
        std::fs::write(p, t).unwrap();
    }
    let Some(outp) = out else { return; };
    if b.aig.ands.is_empty() || b.pos.is_empty() {
        println!("nothing to rewrite (no gates, or none observed): the output is the residual");
        let mut cls2: Vec<Vec<i32>> = if b.aig.ands.is_empty() { cls.clone() } else { b.residual.iter().map(|&i| cls[i].clone()).collect() };
        cls2.extend(units);
        write_cnf(&outp, nv, &cls2).unwrap();
        return;
    }
    let abc = abc.expect("--abc is required with --out");
    let dir = match &keep { Some(d) => { std::fs::create_dir_all(d).unwrap(); d.clone() }
                            None => { let d = std::env::temp_dir().join(format!("cnf2aig_{}", std::process::id())); std::fs::create_dir_all(&d).unwrap(); d.to_string_lossy().to_string() } };
    // ABC runs in that directory (it leaves an abc.history where it runs)
    let dir = std::fs::canonicalize(&dir).map(|d| d.to_string_lossy().to_string()).unwrap_or(dir);
    let in_aig = format!("{dir}/in.aig"); let out_aig = format!("{dir}/out.aig"); let gia = format!("{dir}/out.gia.aig"); let abccnf = format!("{dir}/out.abc.cnf");
    write_aig(&in_aig, &b).unwrap();
    let s = script_for(&script);
    let mut steps = vec![format!("read_aiger {in_aig}"), "strash".to_string()];
    if !s.is_empty() { steps.push(s.to_string()); steps.push("strash".to_string()); }
    steps.push(format!("write_aiger {out_aig}"));
    steps.push("&get".to_string()); steps.push(format!("&w {gia}")); steps.push(format!("&write_cnf -i -o {abccnf}"));
    let t1 = std::time::Instant::now();
    let abc = std::fs::canonicalize(&abc).map(|a| a.to_string_lossy().to_string()).unwrap_or(abc);
    let r = Command::new(&abc).current_dir(&dir).arg("-q").arg(steps.join("; ")).output().unwrap_or_else(|e| { eprintln!("abc: {e}"); std::process::exit(2) });
    if !r.status.success() || !std::path::Path::new(&gia).exists() {
        eprintln!("abc failed: {} {}", String::from_utf8_lossy(&r.stdout), String::from_utf8_lossy(&r.stderr));
        std::process::exit(1);
    }
    let (gi, go, ga, _) = read_aiger(&gia).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(1) });
    let (_, _, a2, _) = read_aiger(&out_aig).unwrap();
    println!("abc [{script}]: {a2} ands ({} before), {:.1}s", b.aig.ands.len(), t1.elapsed().as_secs_f64());
    assert!(gi == b.pis.len() && go == b.pos.len(), "the GIA's inputs/outputs do not match");
    let (nv2, mut cls2) = abc_cnf_to_cnf(nv, &abccnf, &b.pis, &b.pos, gi, ga).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(1) });
    for &i in &b.residual { cls2.push(cls[i].clone()); }
    cls2.extend(units);
    write_cnf(&outp, nv2, &cls2).unwrap();
    println!("-> {outp}: {nv2} vars, {} clauses ({:.1}s)", cls2.len(), t0.elapsed().as_secs_f64());
    if keep.is_none() { let _ = std::fs::remove_dir_all(&dir); }
}

