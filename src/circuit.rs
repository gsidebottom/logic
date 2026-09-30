//! The circuit behind a CNF, and what can be done with it while carrying
//! a proof: the gates read off the clauses (AND/OR of any width by pattern,
//! XOR by same-scope groups, any function of up to three inputs by truth
//! table), structural hashing (`recode`), certified SAT sweeping (`sweep`),
//! select factoring (`factor`), the cut-based writer (`write_cuts`), one
//! pass or several in a row (`pass`, `chain`), each with a DRAT prefix that
//! derives its output from its input.  The command line is `cnf2aig`; the
//! solver's circuit stage (`sat -b hydra_circuit_satsuma`) calls this.
//!
//! doc/data/certified_preprocessing_2026-09-29.txt has the measurements.

use crate::cadical::solver::{Solver, Timeout};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::io::Write;

// ── clauses: flat storage, literals as DIMACS ints ────────────────────────

pub struct Cnf {
    pub nv: usize,
    pub lits: Vec<i32>,
    pub start: Vec<usize>, // clause i = lits[start[i]..start[i+1]]
}

impl Cnf {
    pub fn from_clauses(nv: usize, cls: &[Vec<i32>]) -> Cnf {
        let mut lits = Vec::with_capacity(cls.iter().map(|c| c.len()).sum());
        let mut start = Vec::with_capacity(cls.len() + 1);
        start.push(0);
        for c in cls { lits.extend_from_slice(c); start.push(lits.len()); }
        Cnf { nv, lits, start }
    }
    pub fn len(&self) -> usize { self.start.len() - 1 }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    pub fn clause(&self, i: usize) -> &[i32] { &self.lits[self.start[i]..self.start[i + 1]] }
}

pub fn parse_dimacs(bytes: &[u8]) -> Result<Cnf, String> {
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

pub fn write_cnf(path: &str, nv: usize, cls: &[Vec<i32>]) -> Result<(), String> {
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
pub fn normalize(c: &mut Vec<i32>) -> bool {
    c.sort_unstable_by_key(|l| (l.unsigned_abs(), *l));
    c.dedup();
    c.windows(2).any(|w| w[0] == -w[1])
}

// ── root simplification: units to a fixpoint, tautologies out ─────────────

pub struct Root {
    pub cls: Vec<Vec<i32>>,
    pub origin: Vec<usize>, // cls[j] came from the input clause origin[j]
    pub units: Vec<i32>,
    pub unsat: bool,
}

pub fn simplify_root(cnf: &Cnf) -> Root {
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
    // an empty clause in the input is a contradiction already
    let mut unsat = alive.iter().zip(&dedup).any(|(&a, c)| a && c.is_empty());
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
pub struct Gate {
    pub out: u32,
    pub inputs: Vec<i32>,   // literals for AND (fn = all inputs true, output 'pos'); variables otherwise
    pub clauses: Vec<usize>,
    pub kind: Kind,
}

#[derive(Clone)]
pub enum Kind {
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
pub fn extract_pattern(cls: &[Vec<i32>], xor: bool) -> Vec<Gate> {
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
            // every sign pattern of that parity once: four clauses, not two of them twice
            let signs: HashSet<u32> = group.iter().map(|c| c.iter().fold(0u32, |m, &l| if l > 0 { m | 1 << scope.iter().position(|&v| v == l.unsigned_abs()).unwrap() } else { m })).collect();
            if signs.len() != want { continue; }
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
pub fn extract_generic(cls: &[Vec<i32>], gates: &mut Vec<Gate>, max_inputs: usize) {
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

pub const NONE: u32 = u32::MAX;

/// The gates in topological order, and for every variable the gate that
/// defines it (NONE for an input).  A cycle of definitions is broken at one
/// of its gates: that gate is given up, its output is an input and its
/// clauses are plain clauses again; the gates that depend on it stay.
/// Depth first over the definitions: a gate met again while its own
/// definition is still being followed closes a cycle.
pub fn acyclic_order(gates: &[Gate], nv: usize) -> (Vec<u32>, Vec<u32>) {
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

pub fn max_var(cls: &[Vec<i32>], gates: &[Gate]) -> usize {
    let a = cls.iter().flat_map(|c| c.iter()).map(|l| l.unsigned_abs()).max().unwrap_or(0);
    let b = gates.iter().map(|g| g.out).max().unwrap_or(0);
    a.max(b) as usize
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

pub struct Proof { pub buf: Vec<u8>, pub lemmas: usize }
impl Proof {
    pub fn add(&mut self, c: &[i32]) { let mut l = String::new(); for x in c { let _ = write!(l, "{x} "); } l.push_str("0\n"); self.buf.extend_from_slice(l.as_bytes()); self.lemmas += 1; }
    pub fn del(&mut self, c: &[i32]) { let mut l = String::from("d "); for x in c { let _ = write!(l, "{x} "); } l.push_str("0\n"); self.buf.extend_from_slice(l.as_bytes()); }
}

/// The same proof in the binary DRAT format ('a' or 'd', the literals as
/// 2*variable + sign in groups of seven bits, 0): what a solver's binary
/// proof is appended to.
pub fn binary_drat(text: &[u8]) -> Vec<u8> {
    let mut out: Vec<u8> = Vec::with_capacity(text.len() / 2);
    for line in text.split(|&b| b == b'\n') {
        if line.is_empty() { continue; }
        let (tag, rest) = if line.starts_with(b"d ") { (b'd', &line[2..]) } else { (b'a', line) };
        out.push(tag);
        for tok in rest.split(|&b| b == b' ') {
            if tok.is_empty() { continue; }
            let l: i64 = std::str::from_utf8(tok).unwrap().parse().unwrap();
            if l == 0 { break; }
            let mut u: u64 = 2 * l.unsigned_abs() + (l < 0) as u64;
            while u >= 128 { out.push((u & 127) as u8 | 128); u >>= 7; }
            out.push(u as u8);
        }
        out.push(0);
    }
    out
}

pub fn write_proof(path: &str, proof: &Proof, binary: bool) {
    let r = if binary { std::fs::write(path, binary_drat(&proof.buf)) } else { std::fs::write(path, &proof.buf) };
    r.unwrap_or_else(|e| { eprintln!("{path}: {e}"); std::process::exit(2) });
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

pub struct Recode { cls: Vec<Vec<i32>>, dropped: Vec<Vec<i32>>, merged: usize, dead: usize }

pub fn recode(cnf: &Cnf, root: &Root, gates: &[Gate], proof: &mut Proof) -> Recode {
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

pub struct SweepParams { pub rounds: usize, pub first_window: usize, pub max_window: usize, pub conflicts: i32, pub tries: usize, pub seconds: f64, pub recycle: usize, pub levels: bool, pub give_up: u32 }

#[derive(Default)]
pub struct SweepStats { attempts: usize, merged: usize, constants: usize, refuted: usize, window_sat: usize, unknown: usize, solver_lemmas: usize, splits: usize, shortened: usize, unreached: usize, given_up: usize, whole: usize, solvers: usize, clock: [f64; 4], rounds: usize }

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
        for c in 0..n0 { self.refine_one(c, word); }
        self.members.len() - n0
    }

    /// Split one class by a word of patterns (the others do not need to
    /// have been simulated); how many classes that made.
    fn refine_one(&mut self, c: usize, word: &[u64]) -> usize {
        if self.members[c].len() < 2 { return 0; }
        let w0 = word[self.members[c][0] as usize];
        if self.members[c].iter().all(|&v| word[v as usize] == w0) { return 0; }
        let n0 = self.members.len();
        let mut groups: HashMap<u64, u32> = HashMap::new();
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
pub fn eval_gate(g: &Gate, val: &[u64]) -> u64 {
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

pub fn sweep(cnf: &Cnf, root: &Root, gates: &[Gate], p: &SweepParams, proof: &mut Proof, t0: std::time::Instant, log: &mut dyn FnMut(&str)) -> (Recode, SweepStats) {
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
    // more random patterns while they still split classes: a pattern costs
    // one pass over the circuit, a counterexample a call to the solver and
    // the same pass
    let mut quiet = 0;
    let mut extra = 0usize;
    let simulating = std::time::Instant::now();
    while extra < 240 && quiet < 3 {
        for v in 1..=nv { if gate_of[v] == NONE { val[v] = rng.next(); } }
        for &o in &order { val[o as usize] = eval_gate(&gates[gate_of[o as usize] as usize], &val); }
        for v in 1..=nv { if phase[v] { val[v] = !val[v]; } }
        val[0] = 0;
        let shared = classes.members.iter().filter(|m| m.len() > 1).count();
        let splits = classes.refine(&val);
        if splits * 1000 < shared.max(1000) { quiet += 1; } else { quiet = 0; }
        extra += 1;
    }
    let rounds = p.rounds.max(1) + extra;
    // what a pass over the whole circuit costs
    let pass = simulating.elapsed().as_secs_f64() / extra.max(1) as f64;

    let mut sw = Sweeper { cls, gates, gate_of, rep: vec![0; nv + 1], cval: vec![0; nv + 1], seen: vec![0; nv + 1], stamp: 0,
                           spare: Some(Numbering::new(nv)), cones: None, rested: Some(Numbering::new(nv)), loaded: vec![0; nv + 1],
                           whole: 0, solvers: 0, last_cone: 0, clock: [0.0; 4], p };
    let mut st = SweepStats::default();
    let mut const_units: Vec<i32> = Vec::new();
    let mut shortened: HashMap<usize, Vec<i32>> = HashMap::new();
    let mut in_model: Vec<u32> = vec![0; nv + 1];
    let mut model_stamp = 0u32;
    let mut in_cone: Vec<u32> = vec![0; nv + 1];
    let mut cone_stamp = 0u32;
    let mut word: Vec<u64> = vec![0; nv + 1];
    let mut position: Vec<u32> = vec![0; nv + 1];
    for (k, &o) in order.iter().enumerate() { position[o as usize] = k as u32; }
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
                    // the counterexample and 63 patterns near it.  Through the
                    // whole circuit, and every class gets the word, while that
                    // costs no more than a few attempts (it saves some: 897
                    // counterexamples instead of 6,067 on slp-synthesis-aes);
                    // else through what the members of this class depend on.
                    let t = std::time::Instant::now();
                    let attempt = (sw.clock[0] + sw.clock[1] + sw.clock[2]) / st.attempts.max(1) as f64;
                    let everywhere = pass <= 4.0 * attempt;
                    st.refuted += 1;
                    model_stamp += 1;
                    for &(v, b) in &model {
                        in_model[v as usize] = model_stamp;
                        let flips = rng.next() & rng.next() & rng.next() & !1;
                        val[v as usize] = (if b { !0u64 } else { 0 }) ^ flips;
                    }
                    cone_stamp += 1;
                    let mut cone: Vec<u32> = Vec::new();
                    let mut stack: Vec<u32> = classes.members[c].iter().copied().filter(|&v| v != 0).collect();
                    let mut whole = everywhere;
                    if everywhere { stack.clear(); }
                    while let Some(v) = stack.pop() {
                        let vu = v as usize;
                        if in_cone[vu] == cone_stamp { continue; }
                        in_cone[vu] = cone_stamp;
                        if sw.gate_of[vu] == NONE {
                            if in_model[vu] != model_stamp { val[vu] = rng.next(); }
                            continue;
                        }
                        cone.push(v);
                        if cone.len() * 4 > order.len() { whole = true; break; }
                        for &l in &gates[sw.gate_of[vu] as usize].inputs { stack.push(l.unsigned_abs()); }
                    }
                    if whole {
                        for v in 1..=nv { if sw.gate_of[v] == NONE && in_model[v] != model_stamp && in_cone[v] != cone_stamp { val[v] = rng.next(); } }
                        for &g in &order { val[g as usize] = eval_gate(&gates[sw.gate_of[g as usize] as usize], &val); }
                        for v in 1..=nv { if phase[v] { val[v] = !val[v]; } }
                        val[0] = 0;
                        st.splits += classes.refine(&val);
                    } else {
                        cone.sort_unstable_by_key(|&g| position[g as usize]);
                        for &g in &cone { val[g as usize] = eval_gate(&gates[sw.gate_of[g as usize] as usize], &val); }
                        // the members read complemented where their first pattern was 1; the
                        // gates between them are left as computed, for the ones above
                        let members: Vec<u32> = classes.members[c].clone();
                        for &m in &members { if m != 0 && phase[m as usize] { word[m as usize] = !val[m as usize]; } else { word[m as usize] = if m == 0 { 0 } else { val[m as usize] }; } }
                        st.splits += classes.refine_one(c, &word);
                    }
                    sw.clock[3] += t.elapsed().as_secs_f64();
                }
                Outcome::WindowSat => { st.window_sat += 1; undecided += 1; classes.fails[c] += 1; }
                Outcome::Unknown => { st.unknown += 1; undecided += 1; classes.fails[c] += 1; }
            }
        }
        if !done { let c = classes.id[ou] as usize; classes.reps[c].push(o); }
        if last.elapsed().as_secs() >= 30 {
            last = std::time::Instant::now();
            log(&format!("  sweep: {}/{} gates, {} attempts: {} merged, {} constant, {} refuted, {} undecided ({:.0}s: windows {:.0}, loading {:.0}, whole cones {:.0} ({} calls, {} gates held), simulation {:.0})",
                     n + 1, order.len(), st.attempts, st.merged, st.constants, st.refuted, st.window_sat + st.unknown, t0.elapsed().as_secs_f64(),
                     sw.clock[0], sw.clock[1], sw.clock[2], sw.whole, sw.cones.as_ref().map(|s| s.gates).unwrap_or(0), sw.clock[3]));
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
    st.rounds = rounds;
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

// ── select factoring ─────────────────────────────────────────────────────
//
//   o = s ? (s2 ? a : e) : e      is      o = (s and s2) ? a : e
//
// A circuit written as multiplexers on its inputs hides the products of
// inputs it computes with: the 256 partial products of a 16x16 multiplier
// appear nowhere in gm16spwtrc, and 140,525 of its 320,194 gates are the
// outer half of such a pair.  The product becomes a variable of its own (a
// definition: three clauses, each RAT on the new variable), the outer gate
// a multiplexer on it (clauses that follow from the two old definitions and
// the product's), and the inner gate is dropped where nothing else reads
// it.  A test repeated below itself, o = s ? (s ? a : b) : e, loses the
// branch that cannot be taken.  Only selects that no gate defines are
// paired, so products are of inputs, never of products.

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Branch { Lit(i32), Const(bool) }

fn negated(b: Branch) -> Branch { match b { Branch::Lit(l) => Branch::Lit(-l), Branch::Const(c) => Branch::Const(!c) } }

/// A gate as a multiplexer (select literal, then, else): every way it is one.
fn mux_forms(g: &Gate) -> Vec<(i32, Branch, Branch)> {
    let mut out = Vec::new();
    match &g.kind {
        Kind::And { pos } => {
            if g.inputs.len() != 2 { return out; }
            let (a, b) = (g.inputs[0], g.inputs[1]);
            for (sel, x) in [(a, b), (b, a)] {
                // and(s, x) = s ? x : false
                let f = (sel, Branch::Lit(x), Branch::Const(false));
                out.push(if *pos { f } else { (f.0, negated(f.1), negated(f.2)) });
            }
        }
        Kind::Table(t) => {
            let k = g.inputs.len();
            if !(2..=3).contains(&k) { return out; }
            let value = |assign: &[(usize, usize)]| -> bool {
                let mut row = 0usize;
                for &(j, v) in assign { row |= v << (k - 1 - j); }
                t[row]
            };
            for j in 0..k {
                let others: Vec<usize> = (0..k).filter(|&i| i != j).collect();
                let mut branches = [Branch::Const(false); 2];
                let mut ok = true;
                for (slot, sv) in [(0usize, 1usize), (1, 0)] {
                    // the cofactor: a constant or a literal of one of the other inputs
                    let rows: Vec<Vec<usize>> = if others.len() == 1 { vec![vec![0], vec![1]] } else { vec![vec![0, 0], vec![0, 1], vec![1, 0], vec![1, 1]] };
                    let vals: Vec<bool> = rows.iter().map(|r| {
                        let mut a: Vec<(usize, usize)> = vec![(j, sv)];
                        for (i, &o) in others.iter().enumerate() { a.push((o, r[i])); }
                        value(&a)
                    }).collect();
                    if vals.iter().all(|&v| v == vals[0]) { branches[slot] = Branch::Const(vals[0]); continue; }
                    let mut found = false;
                    for (i, &o) in others.iter().enumerate() {
                        let same = rows.iter().zip(&vals).all(|(r, &v)| v == (r[i] == 1));
                        let flip = rows.iter().zip(&vals).all(|(r, &v)| v == (r[i] == 0));
                        if same { branches[slot] = Branch::Lit(g.inputs[o]); found = true; break; }
                        if flip { branches[slot] = Branch::Lit(-g.inputs[o]); found = true; break; }
                    }
                    if !found { ok = false; break; }
                }
                if ok { out.push((g.inputs[j], branches[0], branches[1])); }
            }
        }
    }
    out
}

/// The clauses of o = sel ? x : y, the two that make o follow from equal
/// branches included; constants evaluated, nothing subsumed left in.
fn mux_clauses(o: i32, sel: i32, x: Branch, y: Branch) -> Vec<Vec<i32>> {
    let lit = |b: Branch, positive: bool| -> Option<Option<i32>> {   // None: the literal is true; Some(None): false
        match b {
            Branch::Const(c) => if c == positive { None } else { Some(None) },
            Branch::Lit(l) => Some(Some(if positive { l } else { -l })),
        }
    };
    let mut raw: Vec<Vec<Option<Option<i32>>>> = vec![
        vec![Some(Some(-sel)), lit(x, false), Some(Some(o))],
        vec![Some(Some(-sel)), lit(x, true), Some(Some(-o))],
        vec![Some(Some(sel)), lit(y, false), Some(Some(o))],
        vec![Some(Some(sel)), lit(y, true), Some(Some(-o))],
        vec![lit(x, false), lit(y, false), Some(Some(o))],
        vec![lit(x, true), lit(y, true), Some(Some(-o))],
    ];
    let mut cls: Vec<Vec<i32>> = Vec::new();
    for c in raw.drain(..) {
        if c.iter().any(|l| l.is_none()) { continue; }
        let mut d: Vec<i32> = c.iter().filter_map(|l| l.unwrap()).collect();
        if normalize(&mut d) { continue; }
        if !cls.contains(&d) { cls.push(d); }
    }
    let keep: Vec<bool> = (0..cls.len()).map(|i| !(0..cls.len()).any(|j| j != i && cls[j].len() < cls[i].len() && cls[j].iter().all(|l| cls[i].contains(l)))).collect();
    cls.into_iter().zip(keep).filter(|(_, k)| *k).map(|(c, _)| c).collect()
}

/// Whether unit propagation over these clauses refutes the lemma's negation.
pub fn follows_by_propagation(clauses: &[&Vec<i32>], lemma: &[i32]) -> bool {
    let mut val: HashMap<u32, bool> = HashMap::new();
    for &l in lemma {
        if let Some(old) = val.insert(l.unsigned_abs(), l < 0) && old != (l < 0) { return true; }
    }
    loop {
        let mut changed = false;
        for c in clauses {
            let mut open = None; let mut n = 0; let mut sat = false;
            for &l in c.iter() {
                match val.get(&l.unsigned_abs()) {
                    Some(&b) => if b == (l > 0) { sat = true; break; },
                    None => { n += 1; open = Some(l); }
                }
            }
            if sat { continue; }
            if n == 0 { return true; }
            if n == 1 { let l = open.unwrap(); val.insert(l.unsigned_abs(), l > 0); changed = true; }
        }
        if !changed { return false; }
    }
}

#[derive(Default)]
pub struct FactorStats { pub paired: usize, pub repeated: usize, pub products: usize, pub dead: usize, pub by_rows: usize }

/// What a gate is rewritten to: select ? then : otherwise.
struct Mux { select: i32, then: Branch, otherwise: Branch, clauses: Vec<Vec<i32>> }

/// A gate that a rule applies to: the gate below it that the rule reads,
/// the two selects to multiply (none for a repeated test, whose select
/// stays), and the branches left.
struct Match { inner: u32, pair: Option<(i32, i32)>, select: i32, then: Branch, otherwise: Branch }

pub fn factor(cnf: &Cnf, root: &Root, gates: &[Gate], proof: &mut Proof) -> (Vec<Vec<i32>>, usize, Vec<Vec<i32>>, FactorStats) {
    let nv = cnf.nv;
    let cls = &root.cls;
    for &u in &root.units { proof.add(&[u]); }
    let (order, gate_of) = acyclic_order(gates, nv);
    let is_gate = |l: i32| (l.unsigned_abs() as usize) <= nv && gate_of[l.unsigned_abs() as usize] != NONE;
    let gate = |v: u32| &gates[gate_of[v as usize] as usize];
    let forms_of = |l: i32| -> Vec<(i32, Branch, Branch)> {
        let f = mux_forms(gate(l.unsigned_abs()));
        if l > 0 { f } else { f.into_iter().map(|(s, a, b)| (s, negated(a), negated(b))).collect() }
    };
    let mut defcl: Vec<bool> = vec![false; cls.len()];
    for &o in &order { for &i in &gate(o).clauses { defcl[i] = true; } }
    let residual: Vec<usize> = (0..cls.len()).filter(|&i| !defcl[i]).collect();

    let mut st = FactorStats::default();
    let mut next = nv;
    let mut product: HashMap<(i32, i32), i32> = HashMap::new();
    let mut product_list: Vec<(i32, [Vec<i32>; 3])> = Vec::new();
    let mut newdef: HashMap<u32, Mux> = HashMap::new();
    for &o in &order {
        let g = gate(o);
        let mut found: Option<Match> = None;
        'forms: for (s, t, e) in mux_forms(g) {
            for (inner, on_then) in [(t, true), (e, false)] {
                let Branch::Lit(il) = inner else { continue };
                if !is_gate(il) { continue; }
                let other = if on_then { e } else { t };
                for (s2, a, b) in forms_of(il) {
                    if s2.unsigned_abs() == s.unsigned_abs() {
                        // the same test again: the branch that can be taken
                        let taken = if (s2 == s) == on_then { a } else { b };
                        found = Some(Match { inner: il.unsigned_abs(), pair: None, select: s, then: if on_then { taken } else { t }, otherwise: if on_then { e } else { taken } });
                        break 'forms;
                    }
                    if is_gate(s) || is_gate(s2) { continue; }
                    let inner = il.unsigned_abs();
                    let hit = |pair: (i32, i32), then: Branch, otherwise: Branch| Some(Match { inner, pair: Some(pair), select: 0, then, otherwise });
                    if on_then {
                        // s ? (s2 ? a : b) : e
                        if b == other { found = hit((s, s2), a, e); break 'forms; }
                        if a == other { found = hit((s, -s2), b, e); break 'forms; }
                    } else {
                        // s ? t : (s2 ? a : b): with a = t it is (s or s2) ? t : b, that is (not s and not s2) ? b : t
                        if a == other { found = hit((-s, -s2), b, t); break 'forms; }
                        if b == other { found = hit((-s, s2), a, t); break 'forms; }
                    }
                }
            }
        }
        let Some(Match { inner, pair, select: sel, then: x, otherwise: y }) = found else { continue };
        if x == y { continue; }   // the gate is one of its inputs: left to the sweep
        let mut support: Vec<&Vec<i32>> = Vec::new();
        for &i in &g.clauses { support.push(&cls[i]); }
        for &i in &gate(inner).clauses { support.push(&cls[i]); }
        let sel = match pair {
            None => { st.repeated += 1; sel }
            Some((l1, l2)) => {
                st.paired += 1;
                let key = if l1.unsigned_abs() < l2.unsigned_abs() { (l1, l2) } else { (l2, l1) };
                *product.entry(key).or_insert_with(|| {
                    next += 1;
                    let p = next as i32;
                    let d = [vec![-p, key.0], vec![-p, key.1], vec![p, -key.0, -key.1]];
                    for c in &d { proof.add(c); }    // each RAT on the new variable, which comes first
                    product_list.push((p, d));
                    p
                })
            }
        };
        let own: Vec<Vec<i32>> = if pair.is_some() { product_list.iter().find(|(p, _)| *p == sel).map(|(_, d)| d.to_vec()).unwrap() } else { Vec::new() };
        for c in &own { support.push(c); }
        let new = mux_clauses(o as i32, sel, x, y);
        for c in &new {
            if follows_by_propagation(&support, c) { proof.add(c); continue; }
            // an encoding that propagation does not see through: by cases on what the gates read
            st.by_rows += 1;
            let mut vars: Vec<u32> = g.inputs.iter().chain(gate(inner).inputs.iter()).map(|l| l.unsigned_abs()).filter(|&v| v != inner).collect();
            vars.sort_unstable(); vars.dedup();
            let vars: Vec<u32> = vars.into_iter().filter(|v| !c.iter().any(|l| l.unsigned_abs() == *v)).collect();
            derive_by_rows(c, &vars, proof);
        }
        newdef.insert(o, Mux { select: sel, then: x, otherwise: y, clauses: new });
    }
    st.products = product_list.len();

    // what the clauses outside the gates read, and what that reads
    let mut needed: Vec<bool> = vec![false; nv + 1];
    let mut stack: Vec<u32> = Vec::new();
    for &i in &residual { for &l in &cls[i] { if is_gate(l) { stack.push(l.unsigned_abs()); } } }
    while let Some(o) = stack.pop() {
        if needed[o as usize] { continue; }
        needed[o as usize] = true;
        match newdef.get(&o) {
            Some(m) => {
                if is_gate(m.select) { stack.push(m.select.unsigned_abs()); }   // a repeated test may be on a gate
                for b in [m.then, m.otherwise] { if let Branch::Lit(l) = b && is_gate(l) { stack.push(l.unsigned_abs()); } }
            }
            None => for &l in &gate(o).inputs { if is_gate(l) { stack.push(l.unsigned_abs()); } },
        }
    }
    let mut keep_original: Vec<bool> = vec![false; cnf.len()];
    let mut out: Vec<Vec<i32>> = Vec::new();
    let mut emit = |i: usize, out: &mut Vec<Vec<i32>>, proof: &mut Proof| {
        let orig = root.origin[i];
        let mut nc = cls[i].clone(); normalize(&mut nc);
        let mut oc: Vec<i32> = cnf.clause(orig).to_vec(); normalize(&mut oc);
        if nc == oc { keep_original[orig] = true; out.push(cnf.clause(orig).to_vec()); return; }
        proof.add(&nc); out.push(nc);
    };
    let mut used: HashSet<i32> = HashSet::new();
    let mut spent: Vec<Vec<i32>> = Vec::new();
    let mut dropped: Vec<Vec<i32>> = Vec::new();
    for &o in &order {
        let alive = needed[o as usize];
        if !alive {
            // its definition goes: a model of the output extends through it
            st.dead += 1;
            for &i in &gate(o).clauses { dropped.push(cls[i].clone()); }
        }
        match newdef.get(&o) {
            Some(m) => {
                if alive { used.insert(m.select); out.extend(m.clauses.iter().cloned()); } else { spent.extend(m.clauses.iter().cloned()); }
            }
            None => if alive { for &i in &gate(o).clauses { emit(i, &mut out, proof); } },
        }
    }
    for (p, d) in &product_list {
        if used.contains(p) { out.extend(d.iter().cloned()); } else { spent.extend(d.iter().cloned()); }
    }
    for &i in &residual { emit(i, &mut out, proof); }
    for &u in &root.units { out.push(vec![u]); }
    let unit_set: HashSet<i32> = root.units.iter().copied().collect();
    for (i, &kept_as_is) in keep_original.iter().enumerate() {
        let c = cnf.clause(i);
        if c.len() == 1 && unit_set.contains(&c[0]) { continue; }
        if !kept_as_is { proof.del(c); }
    }
    for c in &spent { proof.del(c); }
    (out, next, dropped, st)
}

// ── the cut-based writer ──────────────────────────────────────────────────
//
// A variable for every gate and the clauses of its definition is one way to
// write a circuit.  Another (Een, Mishchenko, Sorensson 2007; ABC's
// &write_cnf): choose the gates that keep their variable, the roots, each a
// function of at most K roots and inputs below it, its cut; write that
// function as the cubes of an irredundant cover of it and of one of its
// complement, a clause each; the gates between a root and its cut lose
// their variable.  The roots are chosen for the fewest clauses: every gate
// gets its cuts from the cuts of what it reads, a cut costs its clauses and
// a share of what its leaves cost (area flow), and the choice starts at
// what the clauses outside the gates read.
//
// The proof.  A clause of a root follows from the definitions of the gates
// between the root and its cut: by unit propagation (checked here), else by
// cases on the cut's variables that the clause does not mention, until
// propagation does it -- with all of them given, every gate in between is
// propagated in turn.  The definitions are deleted after the last clause.
// A cover's clause that is one of the root's own is kept as it is: for a
// cut of the root's own inputs the proof is deletions only.
//
// For that to hold the function of a cut is the function of the gates
// between: a cut put together from the cuts of what a gate reads may hold a
// gate and, through another path, what that gate reads, and the function
// put together the same way is then right where the two agree and
// arbitrary elsewhere -- enough for a sound formula, not for a derivation
// from the gates between.  So the leaves are those that are reached from
// the root without passing another, and the function is evaluated from
// them.

const VARS: [u64; 6] = [0xAAAA_AAAA_AAAA_AAAA, 0xCCCC_CCCC_CCCC_CCCC, 0xF0F0_F0F0_F0F0_F0F0,
                        0xFF00_FF00_FF00_FF00, 0xFFFF_0000_FFFF_0000, 0xFFFF_FFFF_0000_0000];
const MAXK: usize = 6;

fn cof0(t: u64, v: usize) -> u64 { let lo = t & !VARS[v]; lo | (lo << (1u32 << v)) }
fn cof1(t: u64, v: usize) -> u64 { let hi = t & VARS[v]; hi | (hi >> (1u32 << v)) }

/// An irredundant cover of a function between `l` and `u` (Minato-Morreale),
/// of the variables below `top`: its cubes as (variables, polarities) are
/// added to `cubes`, the function it covers is returned.
fn isop(l: u64, u: u64, top: usize, cubes: &mut Vec<(u8, u8)>) -> u64 {
    if l == 0 { return 0; }
    if u == !0 { cubes.push((0, 0)); return !0; }
    let Some(v) = (0..top).rev().find(|&v| cof0(l, v) != cof1(l, v) || cof0(u, v) != cof1(u, v)) else {
        cubes.push((0, 0));
        return !0;
    };
    let (l0, l1, u0, u1) = (cof0(l, v), cof1(l, v), cof0(u, v), cof1(u, v));
    let a = cubes.len();
    let r0 = isop(l0 & !u1, u0, v, cubes);
    let b = cubes.len();
    let r1 = isop(l1 & !u0, u1, v, cubes);
    let c = cubes.len();
    let r2 = isop((l0 & !r0) | (l1 & !r1), u0 & u1, v, cubes);
    for q in &mut cubes[a..b] { q.0 |= 1 << v; }
    for q in &mut cubes[b..c] { q.0 |= 1 << v; q.1 |= 1 << v; }
    (r0 & !VARS[v]) | (r1 & VARS[v]) | r2
}

/// The covers of a function and of its complement.
type Cover = (Vec<(u8, u8)>, Vec<(u8, u8)>);

fn cover(memo: &mut HashMap<u64, Cover>, tt: u64) -> &Cover {
    memo.entry(tt).or_insert_with(|| {
        let (mut on, mut off) = (Vec::new(), Vec::new());
        let f = isop(tt, tt, MAXK, &mut on);
        let g = isop(!tt, !tt, MAXK, &mut off);
        assert!(f == tt && g == !tt, "the cover is not the function");
        (on, off)
    })
}

#[derive(Clone, Copy)]
struct Cut { n: u8, leaves: [u32; MAXK], tt: u64, cost: u32, flow: f32 }

impl Cut {
    fn leaves(&self) -> &[u32] { &self.leaves[..self.n as usize] }
    fn trivial(v: u32) -> Cut { let mut leaves = [0; MAXK]; leaves[0] = v; Cut { n: 1, leaves, tt: VARS[0], cost: 0, flow: 0.0 } }
    /// The leaves the function depends on.
    fn used(&self) -> impl Iterator<Item = u32> + '_ {
        let tt = self.tt;
        self.leaves().iter().enumerate().filter(move |(i, _)| cof0(tt, *i) != cof1(tt, *i)).map(|(_, &v)| v)
    }
}

pub struct CutParams { pub leaves: usize, pub limit: usize }

#[derive(Default)]
pub struct CutStats { gates: usize, roots: usize, own: usize, merged: usize, kept: usize, derived: usize, by_cases: usize, case_lemmas: usize, functions: usize }

/// A clause that follows from `support`: by unit propagation, or by cases on
/// the variables of `split` until propagation does it.  The lines of the
/// derivation go to `lines` (the lemmas for the cases are deleted again);
/// false, and nothing written, when no such case analysis does it.
fn derive_by_cases(target: &[i32], split: &[u32], support: &[&Vec<i32>], lines: &mut Vec<(bool, Vec<i32>)>) -> bool {
    if follows_by_propagation(support, target) { lines.push((false, target.to_vec())); return true; }
    let Some((&v, rest)) = split.split_first() else { return false };
    let mark = lines.len();
    let mut halves: Vec<Vec<i32>> = Vec::with_capacity(2);
    for l in [v as i32, -(v as i32)] {
        let mut c = target.to_vec();
        c.push(l);
        if !derive_by_cases(&c, rest, support, lines) { lines.truncate(mark); return false; }
        halves.push(c);
    }
    lines.push((false, target.to_vec()));
    for c in halves { lines.push((true, c)); }
    true
}

pub struct Written { cls: Vec<Vec<i32>>, dropped: Vec<Vec<i32>>, stats: CutStats }

pub fn write_cuts(cnf: &Cnf, root: &Root, gates: &[Gate], p: &CutParams, proof: &mut Proof) -> Written {
    let nv = cnf.nv;
    let cls = &root.cls;
    let k = p.leaves.clamp(2, MAXK);
    for &u in &root.units { proof.add(&[u]); }
    let (order, gate_of) = acyclic_order(gates, nv);
    let gate = |v: u32| &gates[gate_of[v as usize] as usize];
    let is_gate = |v: u32| gate_of[v as usize] != NONE;
    let mut defcl: Vec<bool> = vec![false; cls.len()];
    for &o in &order { for &i in &gate(o).clauses { defcl[i] = true; } }
    let residual: Vec<usize> = (0..cls.len()).filter(|&i| !defcl[i]).collect();
    let mut observed: Vec<bool> = vec![false; nv + 1];
    for &i in &residual { for &l in &cls[i] { if is_gate(l.unsigned_abs()) { observed[l.unsigned_abs() as usize] = true; } } }
    let mut st = CutStats { gates: order.len(), ..Default::default() };

    // who reads whom, to begin with: every gate a root
    let mut refs: Vec<f32> = vec![0.0; nv + 1];
    for &o in &order { for l in &gate(o).inputs { refs[l.unsigned_abs() as usize] += 1.0; } }
    for v in 1..=nv { if observed[v] { refs[v] += 1.0; } }

    // the cuts of every gate, from the cuts of what it reads
    let mut memo: HashMap<u64, Cover> = HashMap::new();
    let mut start: Vec<u32> = vec![0; nv + 2];       // the cuts of a gate: all[start[v]..start[v] + count[v]], its own variable first
    let mut count: Vec<u8> = vec![0; nv + 1];
    let mut all: Vec<Cut> = Vec::new();
    let mut flow: Vec<f32> = vec![0.0; nv + 1];       // what a gate costs as a leaf; nothing for an input
    let mut val: Vec<u64> = vec![0; nv + 1];
    let mut leaf: Vec<u32> = vec![0; nv + 1];
    let mut seen: Vec<u32> = vec![0; nv + 1];
    let mut stamp = 0u32;
    let own_cost = |o: u32| gate(o).clauses.len() as f32;
    for &o in &order {
        let g = gate(o);
        let mut fanins: Vec<u32> = g.inputs.iter().map(|l| l.unsigned_abs()).collect();
        fanins.sort_unstable(); fanins.dedup();
        let first = all.len();
        all.push(Cut::trivial(o));
        let mut found: Vec<Cut> = Vec::new();
        if fanins.len() <= 3 && fanins.len() <= k {
            // one cut of every gate it reads, in every combination
            let lists: Vec<Vec<Cut>> = fanins.iter().map(|&f| {
                if is_gate(f) { all[start[f as usize] as usize..start[f as usize] as usize + count[f as usize] as usize].to_vec() } else { vec![Cut::trivial(f)] }
            }).collect();
            let mut pick = vec![0usize; lists.len()];
            let mut tried: Vec<Vec<u32>> = Vec::new();
            'combos: loop {
                let mut merged: Vec<u32> = Vec::with_capacity(3 * MAXK);
                for (j, &i) in pick.iter().enumerate() { merged.extend_from_slice(lists[j][i].leaves()); }
                merged.sort_unstable(); merged.dedup();
                if merged.len() <= k && !tried.contains(&merged) {
                    // the gates between, first to last, and the leaves they reach
                    stamp += 1;
                    for &l in &merged { leaf[l as usize] = stamp; }
                    let mut between: Vec<u32> = Vec::new();
                    let mut reached: Vec<u32> = Vec::new();
                    let mut walk: Vec<(u32, usize)> = vec![(o, 0)];
                    seen[o as usize] = stamp;
                    let mut cuts_it = true;
                    while let Some(top) = walk.last_mut() {
                        let ins = &gate(top.0).inputs;
                        if top.1 == ins.len() { between.push(top.0); walk.pop(); continue; }
                        let v = ins[top.1].unsigned_abs();
                        top.1 += 1;
                        if seen[v as usize] == stamp { continue; }
                        seen[v as usize] = stamp;
                        if leaf[v as usize] == stamp { reached.push(v); continue; }
                        if !is_gate(v) || between.len() + walk.len() > 64 { cuts_it = false; break; }
                        walk.push((v, 0));
                    }
                    tried.push(merged);
                    reached.sort_unstable();
                    if cuts_it && !found.iter().any(|c| c.leaves().iter().all(|l| reached.contains(l))) {
                        for (i, &l) in reached.iter().enumerate() { val[l as usize] = VARS[i]; }
                        for &b in &between { val[b as usize] = eval_gate(gate(b), &val); }
                        let tt = val[o as usize];
                        let cv = cover(&mut memo, tt);
                        let mut c = Cut { n: reached.len() as u8, leaves: [0; MAXK], tt, cost: (cv.0.len() + cv.1.len()) as u32, flow: 0.0 };
                        c.leaves[..reached.len()].copy_from_slice(&reached);
                        c.flow = c.cost as f32 + c.used().map(|l| flow[l as usize] / refs[l as usize].max(1.0)).sum::<f32>();
                        found.retain(|d| !c.leaves().iter().all(|l| d.leaves().contains(l)));   // a cut within another makes it useless
                        found.push(c);
                    }
                }
                // the next combination
                let mut j = 0;
                loop {
                    if j == pick.len() { break 'combos; }
                    pick[j] += 1;
                    if pick[j] < lists[j].len() { break; }
                    pick[j] = 0;
                    j += 1;
                }
            }
            found.sort_by(|a, b| a.flow.total_cmp(&b.flow).then(a.n.cmp(&b.n)));
            found.truncate(p.limit.clamp(1, 200));
        }
        flow[o as usize] = match found.first() {
            Some(c) => c.flow,
            None => own_cost(o) + fanins.iter().map(|&l| flow[l as usize] / refs[l as usize].max(1.0)).sum::<f32>(),
        };
        all.extend(found);
        start[o as usize] = first as u32;
        count[o as usize] = (all.len() - first) as u8;
    }
    st.functions = memo.len();

    // the roots: what is read from outside the gates, and the cuts of the roots;
    // then the flows again with the readers this choice gives, three times
    let mut best: Vec<u32> = vec![NONE; nv + 1];       // the cut a root is written with; NONE: with its own clauses
    let mut is_root: Vec<bool> = vec![false; nv + 1];
    let mut total = usize::MAX;
    for _ in 0..4 {
        let mut choice: Vec<u32> = vec![NONE; nv + 1];
        for &o in &order {
            let (a, n) = (start[o as usize] as usize, count[o as usize] as usize);
            let mut least = f32::INFINITY;
            for (i, c) in all.iter_mut().enumerate().take(a + n).skip(a + 1) {
                c.flow = c.cost as f32 + c.used().map(|l| flow[l as usize] / refs[l as usize].max(1.0)).sum::<f32>();
                if c.flow < least { least = c.flow; choice[o as usize] = i as u32; }
            }
            flow[o as usize] = if n > 1 { least } else {
                own_cost(o) + gate(o).inputs.iter().map(|l| flow[l.unsigned_abs() as usize] / refs[l.unsigned_abs() as usize].max(1.0)).sum::<f32>()
            };
        }
        let mut wanted: Vec<bool> = observed.clone();
        let mut readers: Vec<f32> = vec![0.0; nv + 1];
        for v in 1..=nv { if observed[v] { readers[v] += 1.0; } }
        let mut clauses = 0usize;
        for &o in order.iter().rev() {
            if !wanted[o as usize] { continue; }
            let mut read = |l: u32| { readers[l as usize] += 1.0; if is_gate(l) { wanted[l as usize] = true; } };
            match choice[o as usize] {
                NONE => { clauses += gate(o).clauses.len(); for l in &gate(o).inputs { read(l.unsigned_abs()); } }
                i => { clauses += all[i as usize].cost as usize; for l in all[i as usize].used() { read(l); } }
            }
        }
        if clauses < total { total = clauses; best = choice; is_root = wanted; }
        for v in 1..=nv { refs[v] = (refs[v] + 2.0 * readers[v]) / 3.0; }
    }

    // the clauses
    let mut keep_original: Vec<bool> = vec![false; cnf.len()];
    let mut out: Vec<Vec<i32>> = Vec::new();
    let mut dropped: Vec<Vec<i32>> = Vec::new();
    let mut emit = |i: usize, out: &mut Vec<Vec<i32>>, proof: &mut Proof| {
        let orig = root.origin[i];
        let mut nc = cls[i].clone(); normalize(&mut nc);
        let mut oc: Vec<i32> = cnf.clause(orig).to_vec(); normalize(&mut oc);
        if nc == oc { keep_original[orig] = true; out.push(cnf.clause(orig).to_vec()); return; }
        proof.add(&nc); out.push(nc);
    };
    let mut lines: Vec<(bool, Vec<i32>)> = Vec::new();
    for &o in &order {
        let g = gate(o);
        if !is_root[o as usize] { for &i in &g.clauses { dropped.push(cls[i].clone()); } continue; }
        st.roots += 1;
        if best[o as usize] == NONE {
            st.own += 1;
            for &i in &g.clauses { emit(i, &mut out, proof); }
            continue;
        }
        let cut = all[best[o as usize] as usize];
        // the gates between the root and its cut
        stamp += 1;
        for &l in cut.leaves() { seen[l as usize] = stamp; }
        let mut between: Vec<u32> = vec![o];
        seen[o as usize] = stamp;
        let mut i = 0;
        while i < between.len() {
            for l in &gate(between[i]).inputs {
                let v = l.unsigned_abs();
                if seen[v as usize] != stamp { seen[v as usize] = stamp; assert!(is_gate(v), "a cut that does not cut"); between.push(v); }
            }
            i += 1;
        }
        if between.len() > 1 { st.merged += 1; }
        let support: Vec<&Vec<i32>> = between.iter().flat_map(|&b| gate(b).clauses.iter().map(|&i| &cls[i])).collect();
        let own: Vec<(usize, Vec<i32>)> = g.clauses.iter().map(|&i| { let mut c = cls[i].clone(); normalize(&mut c); (i, c) }).collect();
        let cv = cover(&mut memo, cut.tt).clone();
        for (cubes, head) in [(&cv.0, o as i32), (&cv.1, -(o as i32))] {
            for &(vars, signs) in cubes.iter() {
                let mut c: Vec<i32> = vec![head];
                for (j, &leaf) in cut.leaves().iter().enumerate() {
                    if vars >> j & 1 == 1 { c.push(if signs >> j & 1 == 1 { -(leaf as i32) } else { leaf as i32 }); }
                }
                normalize(&mut c);
                if let Some((i, _)) = own.iter().find(|(_, d)| *d == c) { st.kept += 1; emit(*i, &mut out, proof); continue; }
                let split: Vec<u32> = cut.leaves().iter().copied().filter(|&l| !c.iter().any(|x| x.unsigned_abs() == l)).collect();
                lines.clear();
                assert!(derive_by_cases(&c, &split, &support, &mut lines),
                        "a clause of a cover that does not follow from the gates it covers: root {o}, cut {:?}, function {:#018x}, clause {c:?}, gates between {between:?}, their clauses {support:?}",
                        cut.leaves(), cut.tt);
                if lines.len() > 1 { st.by_cases += 1; st.case_lemmas += lines.iter().filter(|l| !l.0).count() - 1; }
                for (delete, l) in &lines { if *delete { proof.del(l); } else { proof.add(l); } }
                st.derived += 1;
                out.push(c);
            }
        }
    }
    for &i in &residual { emit(i, &mut out, proof); }
    for &u in &root.units { out.push(vec![u]); }
    let unit_set: HashSet<i32> = root.units.iter().copied().collect();
    for (i, &kept_as_is) in keep_original.iter().enumerate() {
        let c = cnf.clause(i);
        if c.len() == 1 && unit_set.contains(&c[0]) { continue; }
        if !kept_as_is { proof.del(c); }
    }
    Written { cls: out, dropped, stats: st }
}

/// Both orientations of the symmetric groups: the one that keeps more gates
/// (XOR groups towards their highest variable, or towards the variable
/// with the fewest occurrences).
pub fn orientation(cls: &[Vec<i32>], t0: std::time::Instant, log: &mut dyn FnMut(&str)) -> bool {
    let nv = cls.iter().flat_map(|c| c.iter()).map(|l| l.unsigned_abs()).max().unwrap_or(0) as usize;
    let mut best: Option<(usize, bool)> = None;
    for (name, xor) in [("highest-variable", true), ("fewest-occurrences", false)] {
        let mut gates = extract_pattern(cls, xor);
        let np = gates.len();
        extract_generic(cls, &mut gates, 3);
        let (order, _) = acyclic_order(&gates, nv);
        let given_up = gates.iter().map(|g| g.out).collect::<HashSet<u32>>().len() - order.len();
        log(&format!("  orientation {name}: {np} by pattern + {} generic, {} given up to break cycles ({:.1}s)", gates.len() - np, given_up, t0.elapsed().as_secs_f64()));
        if best.map(|b| order.len() > b.0).unwrap_or(true) { best = Some((order.len(), xor)); }
        if given_up == 0 { break; }
    }
    let (_, xor) = best.unwrap();
    log(&format!("  orientation kept: {}", if xor { "highest-variable" } else { "fewest-occurrences" }));
    xor
}

/// One pass that carries its proof: the clauses it leaves, the number of
/// variables, and the definitions it dropped (a model of what it leaves
/// extends through them).
/// What the passes are told.
pub struct Params { pub sweep: SweepParams, pub cuts: CutParams }

impl Default for Params {
    fn default() -> Params {
        Params { sweep: SweepParams { rounds: 16, first_window: 64, max_window: usize::MAX, conflicts: 1000, tries: 2, seconds: 0.0, recycle: 1000, levels: true, give_up: 32 },
                 cuts: CutParams { leaves: 6, limit: 8 } }
    }
}

pub fn pass(mode: &str, cnf: &Cnf, base: &str, params: &Params, proof: &mut Proof, t0: std::time::Instant, log: &mut dyn FnMut(&str)) -> (Vec<Vec<i32>>, usize, Vec<Vec<i32>>) {
    let nv = cnf.nv;
    let before = (proof.lemmas, proof.buf.len());
    let root = simplify_root(cnf);
    if root.unsat {
        log(&format!("{base}: contradictory at the root (unit clauses, or an empty clause) -- writing the empty clause"));
        proof.add(&[]);    // follows by unit propagation
        return (vec![vec![]], nv, Vec::new());
    }
    log(&format!("{base}: root simplification: {} units, {} -> {} clauses ({:.1}s)", root.units.len(), cnf.len(), root.cls.len(), t0.elapsed().as_secs_f64()));
    let xor = orientation(&root.cls, t0, log);
    let mut gates = extract_pattern(&root.cls, xor);
    extract_generic(&root.cls, &mut gates, 3);
    let lemmas = |proof: &Proof| (proof.lemmas - before.0, (proof.buf.len() - before.1) as f64 / 1e6);
    match mode {
        "cuts" => {
            let w = write_cuts(cnf, &root, &gates, &params.cuts, proof);
            let st = &w.stats;
            log(&format!("{base}: cuts: {} gates, {} keep their variable ({} over other gates, {} with their own clauses); {} functions",
                         st.gates, st.roots, st.merged, st.own, st.functions));
            log(&format!("{base}: cuts: {} clauses kept, {} derived ({} by cases, {} lemmas for them)", st.kept, st.derived, st.by_cases, st.case_lemmas));
            log(&format!("{base}: cuts: {} clauses -> {} clauses; {} proof lemmas, {:.1} MB of proof ({:.1}s)",
                         cnf.len(), w.cls.len(), lemmas(proof).0, lemmas(proof).1, t0.elapsed().as_secs_f64()));
            (w.cls, nv, w.dropped)
        }
        "factor" => {
            let (fcls, fnv, dropped, st) = factor(cnf, &root, &gates, proof);
            log(&format!("{base}: factor: {} gates on a product of two selects, {} products; {} repeated tests; {} gates no longer read; {} clauses by cases",
                         st.paired, st.products, st.repeated, st.dead, st.by_rows));
            log(&format!("{base}: factor: {} variables, {} clauses -> {} variables, {} clauses; {} proof lemmas, {:.1} MB of proof ({:.1}s)",
                         nv, cnf.len(), fnv, fcls.len(), lemmas(proof).0, lemmas(proof).1, t0.elapsed().as_secs_f64()));
            (fcls, fnv, dropped)
        }
        "sweep" => {
            let (r, st) = sweep(cnf, &root, &gates, &params.sweep, proof, t0, log);
            log(&format!("{base}: sweep: {} attempts: {} merged, {} constant, {} refuted ({} refinements), {} undecided in the window, {} out of budget; {} dead; {} candidates not reached in time, {} in classes given up",
                         st.attempts, st.merged, st.constants, st.refuted, st.splits, st.window_sat, st.unknown, r.dead, st.unreached, st.given_up));
            log(&format!("{base}: sweep: {} words of random patterns; {} of the attempts went to whole cones, in {} solvers; seconds: windows {:.1}, loading {:.1}, whole cones {:.1}, simulation {:.1}",
                         st.rounds, st.whole, st.solvers, st.clock[0], st.clock[1], st.clock[2], st.clock[3]));
            log(&format!("{base}: sweep: {} -> {} clauses, {} proof lemmas ({} from the solver, {} shortened clauses), {:.1} MB of proof ({:.1}s)",
                         cnf.len(), r.cls.len(), lemmas(proof).0, st.solver_lemmas, st.shortened, lemmas(proof).1, t0.elapsed().as_secs_f64()));
            (r.cls, nv, r.dropped)
        }
        _ => {
            let r = recode(cnf, &root, &gates, proof);
            log(&format!("{base}: recode: {} gates merged, {} dead, {} -> {} clauses, {} proof lemmas ({:.1}s)", r.merged, r.dead, cnf.len(), r.cls.len(), lemmas(proof).0, t0.elapsed().as_secs_f64()));
            (r.cls, nv, r.dropped)
        }
    }
}

/// The vendored CaDiCaL, release defaults, on a formula: the verdict (None
/// when the time ran out) and its conflicts; the proof to a file when asked.
pub fn solve_with_cadical(cnf: &Cnf, timeout: f32, proof: Option<&str>) -> (Option<bool>, i64) {
    let mut s: Solver = Solver::new();
    if let Some(p) = proof && !s.trace_proof_to(p) { eprintln!("{p}: cannot write the proof there"); std::process::exit(2); }
    if timeout > 0.0 { s.set_callbacks(Some(Timeout::new(timeout))); }
    s.reserve(cnf.nv as i32);
    for i in 0..cnf.len() { s.add_clause(cnf.clause(i).iter().copied()); }
    let v = s.solve();
    if proof.is_some() { s.close_proof(); }
    (v, s.conflicts())
}

/// Passes in a row: what they leave, one proof for all of them, and the
/// definitions they dropped (a model of what is left extends through
/// them, see `extend_model`).
pub struct Chain { pub cnf: Cnf, pub proof: Proof, pub dropped: Vec<Vec<i32>> }

pub fn chain(cnf: Cnf, passes: &[&str], base: &str, params: &Params, t0: std::time::Instant, log: &mut dyn FnMut(&str)) -> Chain {
    let mut proof = Proof { buf: Vec::new(), lemmas: 0 };
    let mut dropped: Vec<Vec<i32>> = Vec::new();
    let mut cnf = cnf;
    for mode in passes {
        let (cls, nv, gone) = pass(mode, &cnf, base, params, &mut proof, t0, log);
        dropped.extend(gone);
        cnf = Cnf::from_clauses(nv, &cls);
    }
    Chain { cnf, proof, dropped }
}

/// A model of what the passes left, over the variables they dropped: the
/// dropped definitions, with the model's values as units, to CaDiCaL --
/// unit propagation does nearly all of it, and a variable no definition
/// reaches gets whatever the solver picks.  `model[v]` for v in 1..=nv;
/// false when the definitions cannot be satisfied with these values (a
/// defect: the dropped definitions are implied by the formula the passes
/// left).
pub fn extend_model(nv: usize, dropped: &[Vec<i32>], model: &mut Vec<Option<bool>>) -> bool {
    model.resize(nv + 1, None);
    let mut s: Solver = Solver::new();
    s.reserve(nv as i32);
    for (v, x) in model.iter().enumerate().skip(1) {
        if let Some(b) = x { s.add_clause([if *b { v as i32 } else { -(v as i32) }]); }
    }
    for c in dropped { s.add_clause(c.iter().copied()); }
    if s.solve() != Some(true) { return false; }
    for (v, m) in model.iter_mut().enumerate().skip(1) { *m = Some(s.value(v as i32).unwrap_or(false)); }
    true
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A miter of two multiplexer pairs on inputs 1..4: o1 = 1 ? (2 ? 3 : 4) : 4
    /// as nested multiplexers, o2 = (1 and 2) ? 3 : 4 flat; the clause says
    /// they differ (UNSAT), or that they agree with 5 free (SAT).
    fn miter(unsat: bool) -> Cnf {
        let mut cls: Vec<Vec<i32>> = Vec::new();
        let ite = |o: i32, s: i32, a: i32, e: i32| [vec![-s, -a, o], vec![-s, a, -o], vec![s, -e, o], vec![s, e, -o]];
        cls.extend(ite(6, 2, 3, 4));        // inner
        cls.extend(ite(7, 1, 6, 4));        // outer: o1 = 7
        cls.extend([vec![-8, 1], vec![-8, 2], vec![8, -1, -2]]);   // 8 = 1 and 2
        cls.extend(ite(9, 8, 3, 4));        // o2 = 9
        if unsat { cls.extend([vec![-7, 9, 10], vec![7, -9, 10], vec![-7, -9, -10], vec![7, 9, -10], vec![10]]); }   // 10 = 7 xor 9, asserted
        else { cls.extend([vec![-7, 9], vec![7, -9], vec![7, 5]]); }
        Cnf::from_clauses(10, &cls)
    }

    fn holds(cnf: &Cnf, model: &[Option<bool>]) -> bool {
        (0..cnf.len()).all(|i| cnf.clause(i).iter().any(|&l| model[l.unsigned_abs() as usize] == Some(l > 0)))
    }

    #[test]
    fn the_passes_keep_the_verdict_and_their_proof_is_a_refutation() {
        let cnf = miter(true);
        let mut log = |_: &str| {};
        let ch = chain(miter(true), &["factor", "cuts"], "t", &Params::default(), std::time::Instant::now(), &mut log);
        assert_eq!(solve_with_cadical(&ch.cnf, 0.0, None).0, Some(false), "the miter stays unsatisfiable");
        assert!(ch.proof.lemmas > 0);
        // the prefix followed by the solver's proof, checked by drat-trim when it is there
        let Some(drat) = std::env::var_os("PATH").and_then(|p| std::env::split_paths(&p).map(|d| d.join("drat-trim")).find(|f| f.exists())) else { return };
        let dir = std::env::temp_dir().join(format!("circuit_test_{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let (f, solver, full) = (dir.join("f.cnf"), dir.join("solver.drat"), dir.join("full.drat"));
        write_cnf(f.to_str().unwrap(), cnf.nv, &(0..cnf.len()).map(|i| cnf.clause(i).to_vec()).collect::<Vec<_>>()).unwrap();
        assert_eq!(solve_with_cadical(&ch.cnf, 0.0, Some(solver.to_str().unwrap())).0, Some(false));
        let mut bytes = binary_drat(&ch.proof.buf);
        bytes.extend(std::fs::read(&solver).unwrap());
        std::fs::write(&full, bytes).unwrap();
        let out = std::process::Command::new(drat).arg(&f).arg(&full).output().unwrap();
        let _ = std::fs::remove_dir_all(&dir);
        assert!(String::from_utf8_lossy(&out.stdout).contains("s VERIFIED"), "drat-trim rejected the certificate");
    }

    #[test]
    fn a_model_of_what_the_passes_leave_extends_to_the_input() {
        let cnf = miter(false);
        let mut log = |_: &str| {};
        let ch = chain(miter(false), &["factor", "sweep", "cuts"], "t", &Params::default(), std::time::Instant::now(), &mut log);
        let mut s: Solver = Solver::new();
        s.reserve(ch.cnf.nv as i32);
        for i in 0..ch.cnf.len() { s.add_clause(ch.cnf.clause(i).iter().copied()); }
        assert_eq!(s.solve(), Some(true));
        let nv = ch.cnf.nv.max(cnf.nv);
        let mut occurs = vec![false; nv + 1];
        for i in 0..ch.cnf.len() { for &l in ch.cnf.clause(i) { occurs[l.unsigned_abs() as usize] = true; } }
        let mut model: Vec<Option<bool>> = (0..=nv).map(|v| if v > 0 && occurs[v] { s.value(v as i32) } else { None }).collect();
        assert!(extend_model(nv, &ch.dropped, &mut model));
        assert!(holds(&cnf, &model), "the extended model satisfies the input");
    }
}
