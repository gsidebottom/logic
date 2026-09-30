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
//! Four modes need no ABC and carry a proof: `--recode out.cnf` (structural
//! hashing and dead cones), `--sweep out.cnf` (SAT sweeping: functional
//! equivalences found by simulation, each proved by CaDiCaL), `--factor
//! out.cnf` (nested multiplexers on two inputs become one on their product)
//! and `--cuts out.cnf` (fewer variables, each a function of up to six
//! below it, written as the cubes of its covers).
//! With `--proof prefix.drat` they write a DRAT prefix that derives the
//! output from the input; followed by a solver's proof of the output it
//! refutes the input.  The modes chain: one's output is the next one's
//! input, and the prefixes are concatenated in that order.  `--binary`
//! writes the prefix in the binary DRAT format, for a solver's binary proof.
//!
//!   cnf2aig in.cnf --chain factor,sweep,cuts --to out.cnf --proof prefix.drat --binary
//!
//! runs them in a row and writes one prefix, and
//!
//!   cnf2aig in.cnf --chain factor,cuts --certificate full.drat [--timeout S]
//!
//! goes on to run the vendored CaDiCaL on the result and, on UNSAT, writes
//! the prefix and the solver's proof as one refutation of in.cnf.
//!
//!   cnf2aig in.cnf --factor out.cnf --proof prefix.drat     (select factoring, below)
//!   cnf2aig in.cnf --cuts out.cnf --proof prefix.drat       (the cut-based writer, below; the last
//!           [--leaves 6] [--cuts-per-gate 8]                  of a chain: its blocks are not gates)
//!   cnf2aig in.cnf --sweep out.cnf --proof prefix.drat
//!           [--rounds 16 (words of random patterns to start with; more follow
//!           while they split classes)] [--first 64] [--window GATES] [--conflicts 1000] [--tries 2]
//!           [--recycle 1000] [--seconds S] [--order level|depth] [--give-up 32]
//!
//! (--give-up: a class of candidates is left alone after that many attempts
//! in a row ran out of budget.)
use logic::circuit::*;
use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;
use std::io::Write;
use std::process::Command;

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
    let mut factor_out: Option<String> = None;
    let mut cuts_out: Option<String> = None;
    let mut chain: Option<String> = None;
    let mut chain_to: Option<String> = None;
    let mut solve = false; let mut certificate: Option<String> = None; let mut timeout = 0.0f32;
    let mut params = Params::default();
    let mut binary = false;
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
            "--factor" => { factor_out = Some(args[i + 1].clone()); i += 2; }
            "--binary" => { binary = true; i += 1; }
            "--cuts" => { cuts_out = Some(args[i + 1].clone()); i += 2; }
            "--chain" => { chain = Some(args[i + 1].clone()); i += 2; }
            "--to" => { chain_to = Some(args[i + 1].clone()); i += 2; }
            "--solve" => { solve = true; i += 1; }
            "--certificate" => { certificate = Some(args[i + 1].clone()); solve = true; i += 2; }
            "--timeout" => { timeout = args[i + 1].parse().expect("--timeout SECONDS"); i += 2; }
            "--leaves" => { params.cuts.leaves = args[i + 1].parse().expect("--leaves K"); i += 2; }
            "--cuts-per-gate" => { params.cuts.limit = args[i + 1].parse().expect("--cuts-per-gate N"); i += 2; }
            "--rounds" => { params.sweep.rounds = args[i + 1].parse().expect("--rounds N"); i += 2; }
            "--window" => { params.sweep.max_window = args[i + 1].parse().expect("--window N"); i += 2; }
            "--conflicts" => { params.sweep.conflicts = args[i + 1].parse().expect("--conflicts N"); i += 2; }
            "--tries" => { params.sweep.tries = args[i + 1].parse().expect("--tries N"); i += 2; }
            "--seconds" => { params.sweep.seconds = args[i + 1].parse().expect("--seconds S"); i += 2; }
            "--first" => { params.sweep.first_window = args[i + 1].parse().expect("--first N"); i += 2; }
            "--give-up" => { params.sweep.give_up = args[i + 1].parse::<u32>().expect("--give-up N").max(1); i += 2; }
            "--order" => { params.sweep.levels = match args[i + 1].as_str() { "level" => true, "depth" => false, _ => { eprintln!("--order level|depth"); std::process::exit(2) } }; i += 2; }
            "--recycle" => { params.sweep.recycle = args[i + 1].parse::<usize>().expect("--recycle N").max(2); i += 2; }
            s if s.starts_with("--") => { eprintln!("unknown option {s}"); std::process::exit(2); }
            _ => { input = Some(args[i].clone()); i += 1; }
        }
    }
    params.sweep.first_window = params.sweep.first_window.min(params.sweep.max_window).max(1);
    params.sweep.max_window = params.sweep.max_window.max(1);
    let input = input.expect("input CNF");
    let base = std::path::Path::new(&input).file_name().unwrap().to_string_lossy().to_string();
    let t0 = std::time::Instant::now();
    let bytes = std::fs::read(&input).unwrap_or_else(|e| { eprintln!("{input}: {e}"); std::process::exit(2) });
    let cnf = parse_dimacs(&bytes).unwrap_or_else(|e| { eprintln!("{e}"); std::process::exit(2) });
    // the modes that carry a proof, one or several in a row
    let single = [("cuts", &cuts_out), ("factor", &factor_out), ("sweep", &sweep_out), ("recode", &recode_out)];
    let passes: Vec<(String, Option<String>)> = match &chain {
        Some(list) => {
            let names: Vec<String> = list.split(',').map(|n| n.trim().to_string()).filter(|n| !n.is_empty()).collect();
            for n in &names { if !["cuts", "factor", "sweep", "recode"].contains(&n.as_str()) { eprintln!("--chain: {n} is not one of factor, sweep, recode, cuts"); std::process::exit(2); } }
            if names.iter().rev().skip(1).any(|n| n == "cuts") { eprintln!("--chain: cuts is the last pass (its blocks are not gates)"); std::process::exit(2); }
            let last = names.len().saturating_sub(1);
            names.into_iter().enumerate().map(|(k, n)| (n, if k == last { chain_to.clone() } else { None })).collect()
        }
        None => single.iter().filter(|(_, o)| o.is_some()).map(|(n, o)| (n.to_string(), (*o).clone())).take(1).collect(),
    };
    if !passes.is_empty() {
        let mut proof = Proof { buf: Vec::new(), lemmas: 0 };
        let mut dropped: Vec<Vec<i32>> = Vec::new();
        let mut cnf = cnf;
        let (nv0, n0) = (cnf.nv, cnf.len());
        let mut say = |line: &str| println!("{line}");
        for (mode, to) in &passes {
            let (cls, nv, gone) = pass(mode, &cnf, &base, &params, &mut proof, t0, &mut say);
            dropped.extend(gone);
            if let Some(o) = to { write_cnf(o, nv, &cls).unwrap(); }
            cnf = Cnf::from_clauses(nv, &cls);
        }
        if passes.len() > 1 {
            println!("{base}: {}: {} variables, {} clauses -> {} variables, {} clauses; {} proof lemmas, {:.1} MB of proof ({:.1}s)",
                     passes.iter().map(|(m, _)| m.as_str()).collect::<Vec<_>>().join(", "), nv0, n0, cnf.nv, cnf.len(),
                     proof.lemmas, proof.buf.len() as f64 / 1e6, t0.elapsed().as_secs_f64());
        }
        if let Some(pp) = &proof_out { write_proof(pp, &proof, binary); }
        if let Some(dp) = &dropped_out { write_cnf(dp, cnf.nv, &dropped).unwrap(); }
        if solve {
            // CaDiCaL on what the passes leave; its proof after the prefix is a
            // refutation of the input, in one file
            let solver_proof = certificate.as_ref().map(|c| format!("{c}.solver"));
            let (verdict, conflicts) = solve_with_cadical(&cnf, timeout, solver_proof.as_deref());
            println!("{base}: cadical-3.0.1 on the {} clauses: {} after {} conflicts ({:.1}s)",
                     cnf.len(), match verdict { Some(false) => "UNSAT", Some(true) => "SAT", None => "no answer" }, conflicts, t0.elapsed().as_secs_f64());
            if let (Some(false), Some(c)) = (verdict, &certificate) {
                let mut f = std::fs::File::create(c).unwrap_or_else(|e| { eprintln!("{c}: {e}"); std::process::exit(2) });
                f.write_all(&binary_drat(&proof.buf)).unwrap();
                let mut g = std::fs::File::open(solver_proof.as_ref().unwrap()).unwrap();
                std::io::copy(&mut g, &mut f).unwrap();
                let _ = std::fs::remove_file(solver_proof.as_ref().unwrap());
                println!("{base}: certificate {c}: the prefix and the solver's proof, binary DRAT, against {input}");
            } else if let Some(sp) = &solver_proof { let _ = std::fs::remove_file(sp); }
            match verdict { Some(false) => println!("s UNSATISFIABLE"), Some(true) => println!("s SATISFIABLE (of what the passes leave; the model extends through --dropped)"), None => println!("s UNKNOWN") }
        }
        return;
    }
    let nv = cnf.nv;
    let root = simplify_root(&cnf);
    if root.unsat {
        println!("{base}: contradictory at the root (unit clauses, or an empty clause) -- writing the empty clause");
        if let Some(o) = &out { write_cnf(o, nv, &[vec![]]).unwrap(); }
        return;
    }
    let cls = root.cls.clone();
    println!("{base}: root simplification: {} units, {} -> {} clauses ({:.1}s)", root.units.len(), cnf.len(), cls.len(), t0.elapsed().as_secs_f64());
    // both orientations of the symmetric groups, as AIGs: the one that keeps more gates
    let mut best: Option<(usize, Built)> = None;
    for (name, xor) in [("highest-variable", true), ("fewest-occurrences", false)] {
        let mut gates = extract_pattern(&cls, xor);
        let np = gates.len();
        extract_generic(&cls, &mut gates, 3);
        let built = build_aig(&cls, &gates);
        println!("  orientation {name}: {np} by pattern + {} generic, {} given up to break cycles ({:.1}s)", gates.len() - np, built.ncyclic, t0.elapsed().as_secs_f64());
        let kept = built.ngates - built.ncyclic;
        if best.as_ref().map(|b| kept > b.0).unwrap_or(true) { best = Some((kept, built)); }
        if best.as_ref().map(|b| b.1.ncyclic == 0).unwrap_or(false) { break; }
    }
    let (_, b) = best.unwrap();
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

