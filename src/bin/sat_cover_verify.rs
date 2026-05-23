//! `sat-cover-verify` — independent verifier for matrix-method UNSAT
//! certificates emitted by `sat --emit-cover FILE`.
//!
//! # Background
//!
//! The matrix method certifies CNF unsatisfiability by exhibiting a
//! *complementary cover* of all matrix paths.  A matrix path picks
//! one literal from each clause; the cover proves every such path
//! contains some `(X, ¬X)` pair.
//!
//! # Cert format (v3 — var-grouped)
//!
//! The cert is a list of per-variable entries.  Each entry lists the
//! positions where that variable's positive lit appears (as the
//! matrix-method walks the complement NNF) and the positions where
//! its negative lit appears.  Every cross-product of one positive
//! position with one negative position is implicitly a cover pair.
//!
//! ```text
//! v <var> + <c>:<l>[,<l>...] [<c>:<l>...] - <c>:<l>[,<l>...] ...
//! ```
//!
//! Position tokens are clause-grouped: `<c>:<l1>,<l2>,...` means
//! "var X's polarity-positive lit appears at clause c, alt indices
//! l1, l2, ...".  Equivalent to writing `c:l1 c:l2 c:l3` separately.
//!
//! Comments are `# ...` lines.  Whitespace is flexible.
//!
//! ## Compression
//!
//! The v3 format expresses `K_pos × K_neg` pairs per variable using
//! only `K_pos + K_neg` positions.  On industrial inputs (each var
//! appearing at 100+ positions per polarity) this is a ~100× space
//! saving over the flat per-pair format (v2).
//!
//! # Verifier algorithm
//!
//! 1. **Per-entry validity (linear pass)**.  For each `v` line:
//!    - All positions are in bounds: `c < num_clauses`, `l < |F[c]|`.
//!    - All positive-side positions have lit value `+var` (in the
//!      matrix-method complement-walk semantics: `-F[c][l] == +var`).
//!    - All negative-side positions have lit value `-var`.
//!    - The positive and negative sets are non-empty (else this var
//!      contributes nothing).
//!
//! 2. **Completeness (pruned DFS over matrix paths)**.  Track per
//!    variable: how many positive positions have been matched by the
//!    current partial assignment, and how many negative.  When BOTH
//!    counts are > 0 for some variable, the subtree is covered (the
//!    matrix path has both `+X` and `−X` on it).  A running
//!    `active_var_count` keeps the per-step check O(1):
//!    - On push: each (var, polarity) whose set includes the new
//!      position gets its matched-count incremented.  If a var
//!      transitions from "only one polarity active" → "both
//!      polarities active", increment active_var_count.
//!    - On backtrack: reverse the increments; decrement
//!      active_var_count when a var loses the both-polarities
//!      condition.
//!    - At each DFS node, prune iff `active_var_count > 0`.
//!    - If a complete matrix path (all clauses chosen) is reached
//!      without pruning, the cert is incomplete.
//!
//! # Soundness
//!
//! The verifier never executes the prover's controllers (CDCL,
//! Effective, bubble-up).  Its surface area is:
//!
//! - DIMACS parsing (~30 lines).
//! - v3 cert parsing (~50 lines).
//! - Per-entry validation (~30 lines).
//! - Pruned DFS (~80 lines).
//!
//! Disagreement between verifier and prover means the cert is
//! invalid (or the verifier has a bug — but it's small enough to
//! inspect).
//!
//! # CLI
//!
//! ```text
//! sat-cover-verify <cnf-file> <cert-file>
//! ```
//!
//! Exits 0 on valid, 1 on cert error, 2 on usage / I/O error.

use std::env;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::PathBuf;
use std::process::ExitCode;

// ─── CNF parsing ────────────────────────────────────────────────────────────

/// Parsed CNF.  `clauses[i]` is one clause as a vector of DIMACS
/// literals.
struct Cnf {
    nvars:   usize,
    clauses: Vec<Vec<i32>>,
}

fn parse_dimacs<R: BufRead>(r: R) -> Result<Cnf, String> {
    let mut nvars = 0;
    let mut clauses: Vec<Vec<i32>> = Vec::new();
    let mut current: Vec<i32> = Vec::new();
    for (lineno, line) in r.lines().enumerate() {
        let line = line.map_err(|e| format!("read error at line {}: {}", lineno + 1, e))?;
        let t = line.trim();
        if t.is_empty() || t.starts_with('c') || t.starts_with('%') { continue; }
        if let Some(rest) = t.strip_prefix("p cnf ") {
            let mut it = rest.split_ascii_whitespace();
            if let Some(v) = it.next() {
                nvars = v.parse().map_err(|_|
                    format!("line {}: bad nvars in p cnf header", lineno + 1))?;
            }
            continue;
        }
        if t.starts_with("p ") { continue; }
        for tok in t.split_ascii_whitespace() {
            let n: i32 = tok.parse().map_err(|_|
                format!("line {}: not an integer: {:?}", lineno + 1, tok))?;
            if n == 0 {
                if !current.is_empty() {
                    clauses.push(std::mem::take(&mut current));
                }
            } else {
                current.push(n);
            }
        }
    }
    if !current.is_empty() {
        clauses.push(current);
    }
    if nvars == 0 {
        nvars = clauses.iter()
            .flat_map(|c| c.iter())
            .map(|l| l.unsigned_abs() as usize)
            .max()
            .unwrap_or(0);
    }
    Ok(Cnf { nvars, clauses })
}

// ─── Cert parsing (v3) ──────────────────────────────────────────────────────

/// One position `(clause_idx, lit_idx)` in F's complement NNF.
type Position = (usize, usize);

/// One cert var-entry: lists positive-polarity and negative-polarity
/// positions for a single CNF variable.
struct VarEntry {
    var: u32,
    positive: Vec<Position>,
    negative: Vec<Position>,
}

struct Cert {
    vars: Vec<VarEntry>,
}

/// Parse a position token like `<c>:<l1>[,<l2>...]` into one or
/// more positions.  Returns an iterator-style Vec since one token
/// can expand to many positions (clause-grouping).
fn parse_pos_token(tok: &str) -> Result<Vec<Position>, String> {
    let (c_str, rest) = tok.split_once(':').ok_or_else(||
        format!("bad position token {:?}: expected '<c>:<l>[,...]'", tok))?;
    let c: usize = c_str.parse().map_err(|_|
        format!("bad clause index in {:?}", tok))?;
    let mut out = Vec::new();
    for l_str in rest.split(',') {
        let l: usize = l_str.parse().map_err(|_|
            format!("bad lit index in {:?}", tok))?;
        out.push((c, l));
    }
    Ok(out)
}

fn parse_cert<R: BufRead>(r: R) -> Result<Cert, String> {
    let mut vars: Vec<VarEntry> = Vec::new();
    for (lineno, line) in r.lines().enumerate() {
        let line = line.map_err(|e| format!("cert read error line {}: {}", lineno + 1, e))?;
        let t = line.trim();
        if t.is_empty() || t.starts_with('#') { continue; }
        let Some(rest) = t.strip_prefix('v') else {
            return Err(format!("cert line {}: unrecognised line {:?} (expected '# ...' or 'v ...')",
                                lineno + 1, t));
        };
        // Format: `v <var> + <pos> <pos> ... - <pos> <pos> ...`
        let mut toks = rest.split_ascii_whitespace();
        let var: u32 = toks.next()
            .ok_or_else(|| format!("cert line {}: 'v' line missing var", lineno + 1))?
            .parse()
            .map_err(|_| format!("cert line {}: bad var index", lineno + 1))?;
        let mut positive: Vec<Position> = Vec::new();
        let mut negative: Vec<Position> = Vec::new();
        let mut current: Option<bool> = None;   // true = pushing into positive, false = negative
        for tok in toks {
            match tok {
                "+" => current = Some(true),
                "-" => current = Some(false),
                _ => {
                    let positions = parse_pos_token(tok)
                        .map_err(|e| format!("cert line {}: {}", lineno + 1, e))?;
                    match current {
                        Some(true)  => positive.extend(positions),
                        Some(false) => negative.extend(positions),
                        None => return Err(format!(
                            "cert line {}: position token {:?} before any +/- marker",
                            lineno + 1, tok)),
                    }
                }
            }
        }
        vars.push(VarEntry { var, positive, negative });
    }
    Ok(Cert { vars })
}

// ─── Per-entry validity ─────────────────────────────────────────────────────

/// Verify every position in this entry resolves to the expected
/// signed lit value: positive-side positions must visit `+var`,
/// negative-side `−var`.  The matrix-method engine visits the
/// complement NNF, so the lit at `(c, l)` is `−F[c][l]`.
fn validate_entry(f: &Cnf, e: &VarEntry, idx: usize) -> Result<(), String> {
    if e.positive.is_empty() {
        return Err(format!("entry {} (var {}): empty positive side — no implied pairs",
                            idx, e.var));
    }
    if e.negative.is_empty() {
        return Err(format!("entry {} (var {}): empty negative side — no implied pairs",
                            idx, e.var));
    }
    let var_i32 = e.var as i32;
    let check = |pos: &Position, expected_sign: i32, side: &str| -> Result<(), String> {
        let (c, l) = *pos;
        if c >= f.clauses.len() {
            return Err(format!("entry {} (var {}, {}): clause {} out of range",
                                idx, e.var, side, c));
        }
        if l >= f.clauses[c].len() {
            return Err(format!("entry {} (var {}, {}): lit_idx {} out of range for clause {} (arity {})",
                                idx, e.var, side, l, c, f.clauses[c].len()));
        }
        // visited lit = -F[c][l]; we expect expected_sign * var.
        let visited = -f.clauses[c][l];
        let want = expected_sign * var_i32;
        if visited != want {
            return Err(format!("entry {} (var {}, {}): position ({},{}) visits {} but expected {}",
                                idx, e.var, side, c, l, visited, want));
        }
        Ok(())
    };
    for p in &e.positive {
        check(p, 1, "+")?;
    }
    for p in &e.negative {
        check(p, -1, "-")?;
    }
    Ok(())
}

// ─── Completeness check (pruned DFS) ────────────────────────────────────────

/// Per-variable runtime state during the DFS.
struct VarState {
    /// Number of this var's positive-polarity positions currently
    /// matched by the partial assignment.
    pos_matched: u32,
    /// Same for negative-polarity.
    neg_matched: u32,
}

/// Pre-built lookup: position `(c, l)` → list of `(var_idx, is_positive_side)`.
/// var_idx indexes into `var_states` / cert's vars list, not the
/// DIMACS var number.
type PosIndex = std::collections::HashMap<Position, Vec<(usize, bool)>>;

struct CoverDfs<'a> {
    f: &'a Cnf,
    pos_index: PosIndex,
    var_states: Vec<VarState>,
    /// Running count of variables with `pos_matched > 0 && neg_matched > 0`.
    /// `> 0` means some var is currently proving the subtree
    /// covered — prune.
    active_var_count: usize,
}

impl<'a> CoverDfs<'a> {
    fn new(f: &'a Cnf, cert: &'a Cert) -> Self {
        let mut pos_index: PosIndex = std::collections::HashMap::new();
        let mut var_states: Vec<VarState> = Vec::with_capacity(cert.vars.len());
        for (i, entry) in cert.vars.iter().enumerate() {
            for &p in &entry.positive {
                pos_index.entry(p).or_default().push((i, true));
            }
            for &p in &entry.negative {
                pos_index.entry(p).or_default().push((i, false));
            }
            var_states.push(VarState { pos_matched: 0, neg_matched: 0 });
        }
        Self { f, pos_index, var_states, active_var_count: 0 }
    }

    /// Run DFS from the matrix root.  Returns `Ok(())` on validated
    /// complete cover, `Err(path)` with the first uncovered matrix
    /// path (as lit-indices per clause in clause order).
    fn verify(&mut self) -> Result<(), Vec<usize>> {
        let mut partial: Vec<usize> = Vec::with_capacity(self.f.clauses.len());
        self.dfs(0, &mut partial)
    }

    fn dfs(&mut self, clause_idx: usize, partial: &mut Vec<usize>) -> Result<(), Vec<usize>> {
        if self.active_var_count > 0 {
            return Ok(());   // pruned: some var has both polarities matched on partial
        }
        if clause_idx == self.f.clauses.len() {
            return Err(partial.clone());
        }
        let arity = self.f.clauses[clause_idx].len();
        for lit_idx in 0..arity {
            // Apply: increment counts for each (var, side) whose set
            // contains this position.  Track for revert.
            let pos = (clause_idx, lit_idx);
            let touches: Vec<(usize, bool)> = self.pos_index.get(&pos).cloned().unwrap_or_default();
            let mut became_active: Vec<usize> = Vec::new();
            for &(var_idx, is_positive) in &touches {
                let st = &mut self.var_states[var_idx];
                if is_positive {
                    st.pos_matched += 1;
                    if st.pos_matched == 1 && st.neg_matched > 0 {
                        self.active_var_count += 1;
                        became_active.push(var_idx);
                    }
                } else {
                    st.neg_matched += 1;
                    if st.neg_matched == 1 && st.pos_matched > 0 {
                        self.active_var_count += 1;
                        became_active.push(var_idx);
                    }
                }
            }

            partial.push(lit_idx);
            let r = self.dfs(clause_idx + 1, partial);
            partial.pop();

            // Revert in reverse order: undo became_active first, then
            // counter decrements (which can't trigger further became_active
            // changes since we're symmetrically reversing).
            for &var_idx in became_active.iter().rev() {
                self.active_var_count -= 1;
                let _ = var_idx;
            }
            for &(var_idx, is_positive) in touches.iter().rev() {
                let st = &mut self.var_states[var_idx];
                if is_positive {
                    st.pos_matched -= 1;
                } else {
                    st.neg_matched -= 1;
                }
            }

            r?;
        }
        Ok(())
    }
}

// ─── Main ───────────────────────────────────────────────────────────────────

fn main() -> ExitCode {
    let mut args = env::args().skip(1);
    let cnf_path: PathBuf = match args.next() {
        Some(p) => p.into(),
        None => {
            eprintln!("usage: sat-cover-verify <cnf-file> <cert-file>");
            return ExitCode::from(2);
        }
    };
    let cert_path: PathBuf = match args.next() {
        Some(p) => p.into(),
        None => {
            eprintln!("usage: sat-cover-verify <cnf-file> <cert-file>");
            return ExitCode::from(2);
        }
    };

    let f = match File::open(&cnf_path).map_err(|e| e.to_string())
        .and_then(|f| parse_dimacs(BufReader::new(f)))
    {
        Ok(f) => f,
        Err(e) => {
            eprintln!("cnf parse failed ({}): {}", cnf_path.display(), e);
            return ExitCode::from(2);
        }
    };
    eprintln!("c F: vars={} clauses={}", f.nvars, f.clauses.len());

    let cert = match File::open(&cert_path).map_err(|e| e.to_string())
        .and_then(|f| parse_cert(BufReader::new(f)))
    {
        Ok(c) => c,
        Err(e) => {
            eprintln!("cert parse failed ({}): {}", cert_path.display(), e);
            return ExitCode::from(2);
        }
    };
    let total_positions: usize = cert.vars.iter()
        .map(|v| v.positive.len() + v.negative.len()).sum();
    let total_pairs: usize = cert.vars.iter()
        .map(|v| v.positive.len() * v.negative.len()).sum();
    eprintln!("c cert: {} vars, {} positions, {} implied pairs",
              cert.vars.len(), total_positions, total_pairs);

    // Per-entry validation.
    for (i, e) in cert.vars.iter().enumerate() {
        if let Err(msg) = validate_entry(&f, e, i) {
            eprintln!("INVALID CERT (per-entry): {}", msg);
            return ExitCode::from(1);
        }
    }
    eprintln!("c per-entry validity: OK ({} entries)", cert.vars.len());

    // Completeness DFS.
    let mut dfs = CoverDfs::new(&f, &cert);
    let start = std::time::Instant::now();
    match dfs.verify() {
        Ok(()) => {
            let ms = start.elapsed().as_secs_f64() * 1000.0;
            eprintln!("c completeness: OK ({:.1}ms)", ms);
            let _ = writeln!(io::stdout(), "VALID UNSAT CERTIFICATE");
            ExitCode::from(0)
        }
        Err(path) => {
            eprintln!("INCOMPLETE CERT: matrix path not covered by any entry");
            eprint!("  uncovered path (clause:lit_idx → lit):");
            for (c, &l) in path.iter().enumerate() {
                let lit = -f.clauses[c][l];
                eprint!(" {}:{}={}", c, l, lit);
            }
            eprintln!();
            let _ = writeln!(io::stdout(), "INVALID CERTIFICATE (incomplete)");
            ExitCode::from(1)
        }
    }
}
