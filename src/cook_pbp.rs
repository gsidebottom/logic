//! Cook-style polynomial PB proof emission for structured CNFs.
//!
//! For inputs matching the **PHP** (pigeon-hole) or **RoundRobin**
//! cardinality shape, this module emits VeriPB-verifiable polynomial-size
//! UNSAT proofs.  See:
//!   - `tools/cook_php_proof.py` (original Python prototype),
//!   - `tools/cook_rr_proof.py`,
//!   - `doc/cook_php_walkthrough.md` for the proof construction.
//!
//! ## Public API
//!
//! ```ignore
//! use logic::cook_pbp::{detect_shape, CnfShape, emit_proof};
//!
//! let shape = detect_shape(&clauses);
//! match shape {
//!     CnfShape::Php { n, m } => { /* emit Cook PHP proof */ }
//!     CnfShape::RoundRobin { n_teams, n_days } => { /* emit Cook RR proof */ }
//!     CnfShape::Unknown => { /* fall back */ }
//! }
//! emit_proof(&shape, &mut writer)?;
//! ```
//!
//! ## Detection
//!
//! [`detect_shape`] inspects the input CNF and returns the canonical
//! shape if it matches PHP or RoundRobin's standard SAT-competition
//! encoding.  Detection is *exact*: the CNF must match the byte layout
//! the Python generators produce (also matches the official
//! benchmarks for the RoundRobin family).
//!
//! ## Emission
//!
//! For each detected shape, the proof structure follows Cook 1976 +
//! the at-most-1-from-pairwise-mutex subroutine.  See the module's
//! `emit_php` / `emit_roundrobin` functions for details.

use std::io::{self, Write};

// ─── Shape detection ───────────────────────────────────────────────────────

/// Recognised structural shapes for which we have polynomial proofs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CnfShape {
    /// PHP-N-M: N pigeons, M holes (N > M).  Variables `(i-1)*M + j`
    /// for pigeon i ∈ [1, N], hole j ∈ [1, M].  Clauses in load order:
    /// N pigeon clauses, then for each hole h ∈ [1, M] the C(N, 2)
    /// pairwise mutex clauses in lex pair-of-pigeons order.
    Php { n: usize, m: usize },
    /// RoundRobin: n teams × d days.  Variables `pair_idx * d + day + 1`
    /// where `pair_idx` is the 0-indexed lex position of pair (i, j)
    /// with i < j ∈ [0, n).  Clauses in per-pair blocks
    /// (1 pigeon + C(d, 2) pair-day mutex), then per (team, day) ×
    /// C(n-1, 2) team-day mutex.  Matches the official
    /// `RoundRobin_n*_d*.cnf` benchmarks byte-for-byte.
    RoundRobin { n_teams: usize, n_days: usize },
    /// Generic embedded pigeonhole (P disjoint at-least-one clauses + S
    /// complete slot-mutex cliques, P > S).  Generalises PHP/RoundRobin
    /// to e.g. MVRoundRobin; carries the extracted structure because the
    /// variable layout is read from the CNF, not canonical.
    EmbeddedPigeonhole(EmbeddedPigeonhole),
    /// No matching shape detected.
    Unknown,
}

impl CnfShape {
    /// Human-readable description used in proof comments and CLI output.
    pub fn describe(&self) -> String {
        match self {
            CnfShape::Php { n, m } => format!("PHP-{}-{}", n, m),
            CnfShape::RoundRobin { n_teams, n_days } => {
                format!("RoundRobin n={} d={}", n_teams, n_days)
            }
            CnfShape::EmbeddedPigeonhole(ep) => format!(
                "embedded pigeonhole {}x{}",
                ep.pigeon_ids.len(),
                ep.holes.len()
            ),
            CnfShape::Unknown => "Unknown".into(),
        }
    }
}

/// Try to recognise the input CNF as a known structural shape.
///
/// PHP detection: first `n` clauses are arity-`m` disjunctions of
/// `(i-1)*m + 1..=i*m` (one per pigeon), followed by `m * C(n,2)`
/// binary mutex clauses in the expected order.  Returns `Php { n, m }`
/// if the CNF matches byte-exactly.
///
/// RoundRobin detection: looks for the per-pair block structure
/// (pigeon + C(d, 2) pair-day mutex per pair) followed by team-day
/// mutex.  Returns `RoundRobin { n_teams, n_days }` if matching.
///
/// Returns [`CnfShape::Unknown`] otherwise.  Detection is O(clauses).
pub fn detect_shape(clauses: &[Vec<i32>], nvars: usize) -> CnfShape {
    if let Some(s) = detect_php(clauses, nvars) {
        return s;
    }
    if let Some(s) = detect_roundrobin(clauses, nvars) {
        return s;
    }
    if let Some(ep) = detect_embedded_pigeonhole(clauses, nvars) {
        return CnfShape::EmbeddedPigeonhole(ep);
    }
    CnfShape::Unknown
}

/// Heuristic structural test used to *route the `eff` visit-order policy*
/// (not for proof emission).  Returns `true` when the CNF looks like an
/// "exactly-one" cardinality CSP — PHP, RoundRobin, MVRoundRobin,
/// scheduling, graph-colouring-style encodings — i.e. its at-least-one
/// constraints (all-positive clauses of arity ≥ 2) are pairwise
/// variable-DISJOINT (a genuine partition of objects into value groups),
/// and the remaining clauses are overwhelmingly binary at-most-one
/// mutexes.
///
/// These are exactly the highly-symmetric, structured instances where the
/// matrix method's EffectiveCount (path-count) ordering dominates and
/// conflict-driven VSIDS only wastes search effort — so `bin/sat.rs`
/// routes them to pure EffectiveCount instead of the default
/// VSIDS-alternating portfolio.  This generalises past byte-exact
/// PHP/RoundRobin matching: it catches MVRoundRobin and unseen
/// cardinality families too.
///
/// Crucially it does NOT fire on arithmetic/circuit formulas (ezfact,
/// tseitin, the x9 circuit family): their XOR/gate clauses are
/// mixed-polarity and their positive clauses overlap heavily, so the
/// disjoint-partition test fails and they keep the VSIDS portfolio.
/// O(total literals).
pub fn is_exactly_one_csp(clauses: &[Vec<i32>]) -> bool {
    use std::collections::HashSet;
    let mut seen: HashSet<i32> = HashSet::new();
    let mut at_least_one = 0usize;
    let mut non_alo = 0usize;
    let mut bin_neg_mutex = 0usize;
    for c in clauses {
        let all_pos = c.len() >= 2 && c.iter().all(|&l| l > 0);
        if all_pos {
            at_least_one += 1;
            // Reject if this at-least-one clause shares a variable with a
            // *previous* one — then the at-least-one clauses don't form a
            // partition, so it isn't an exactly-one CSP.  (Within-clause
            // dups are harmless: we test against `seen` before inserting
            // any of this clause's vars.)
            for &l in c {
                if seen.contains(&l.abs()) {
                    return false;
                }
            }
            for &l in c {
                seen.insert(l.abs());
            }
        } else {
            non_alo += 1;
            if c.len() == 2 && c.iter().all(|&l| l < 0) {
                bin_neg_mutex += 1;
            }
        }
    }
    // Need a real partition (≥ 2 disjoint groups) and the rest of the
    // formula must be ~all at-most-one mutexes (the cardinality skeleton).
    if at_least_one < 2 {
        return false;
    }
    if non_alo > 0 && (bin_neg_mutex as f64) / (non_alo as f64) < 0.9 {
        return false;
    }
    true
}

fn detect_php(clauses: &[Vec<i32>], nvars: usize) -> Option<CnfShape> {
    // PHP-N-M requires nvars = N*M.  First clause is pigeon 1 (vars 1..=M).
    if clauses.is_empty() { return None; }
    let m = clauses[0].len();
    if m < 2 { return None; }
    if nvars % m != 0 { return None; }
    let n = nvars / m;
    if n <= m { return None; }   // PHP UNSAT requires N > M
    // Expected clause count: N pigeons + M * C(N, 2) mutex.
    let expected_n_clauses = n + m * (n * (n - 1) / 2);
    if clauses.len() != expected_n_clauses { return None; }
    // Check N pigeon clauses.
    for i in 1..=n {
        let want: Vec<i32> = (1..=m).map(|j| ((i - 1) * m + j) as i32).collect();
        if clauses[i - 1] != want { return None; }
    }
    // Check mutex clauses: for each hole h ∈ [1, M], for each pair (p1, p2) lex.
    let mut idx = n;
    for h in 1..=m {
        for p1 in 1..=n {
            for p2 in (p1 + 1)..=n {
                let want = vec![-(((p1 - 1) * m + h) as i32),
                                -(((p2 - 1) * m + h) as i32)];
                if clauses.get(idx) != Some(&want) { return None; }
                idx += 1;
            }
        }
    }
    Some(CnfShape::Php { n, m })
}

fn detect_roundrobin(clauses: &[Vec<i32>], nvars: usize) -> Option<CnfShape> {
    // First clause: pigeon 1 = vars 1..=d (one var per day).
    if clauses.is_empty() { return None; }
    let d = clauses[0].len();
    if d < 1 { return None; }
    // nvars = n_pairs * d.  Find n such that nvars = C(n, 2) * d.
    if nvars % d != 0 { return None; }
    let n_pairs = nvars / d;
    // n_pairs = n*(n-1)/2 → solve for n: n = (1 + sqrt(1 + 8*n_pairs)) / 2
    let disc = 1 + 8 * n_pairs;
    let n_teams_f = ((1.0 + (disc as f64).sqrt()) / 2.0) as usize;
    if n_teams_f * (n_teams_f - 1) / 2 != n_pairs { return None; }
    let n = n_teams_f;
    if n < 2 { return None; }
    // Expected clauses: n_pairs * (1 + C(d, 2)) [per-pair blocks]
    //                 + n * d * C(n-1, 2)        [team-day mutex]
    let pair_block = 1 + d * (d - 1) / 2;
    let team_day = n * d * ((n - 1) * (n - 2) / 2);
    let expected = n_pairs * pair_block + team_day;
    if clauses.len() != expected { return None; }
    // Verify the per-pair blocks.
    let mut idx = 0;
    for p in 0..n_pairs {
        let want_pigeon: Vec<i32> = (0..d).map(|k| (p * d + k + 1) as i32).collect();
        if clauses.get(idx) != Some(&want_pigeon) { return None; }
        idx += 1;
        for k1 in 0..d {
            for k2 in (k1 + 1)..d {
                let want = vec![-((p * d + k1 + 1) as i32),
                                -((p * d + k2 + 1) as i32)];
                if clauses.get(idx) != Some(&want) { return None; }
                idx += 1;
            }
        }
    }
    // Verify the team-day mutex blocks.
    let pairs: Vec<(usize, usize)> = (0..n).flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
        .collect();
    let pair_idx_of = |i: usize, j: usize| -> usize {
        let (i, j) = if i < j { (i, j) } else { (j, i) };
        pairs.iter().position(|&(a, b)| a == i && b == j).unwrap()
    };
    for t in 0..n {
        let mut matches_of_t: Vec<usize> = (0..n_pairs)
            .filter(|&pi| { let (a, b) = pairs[pi]; a == t || b == t })
            .collect();
        matches_of_t.sort();
        for k in 0..d {
            for i in 0..matches_of_t.len() {
                for j in (i + 1)..matches_of_t.len() {
                    let pi = matches_of_t[i];
                    let pj = matches_of_t[j];
                    let _ = pair_idx_of;   // (helper unused; kept for parity)
                    let want = vec![-((pi * d + k + 1) as i32),
                                    -((pj * d + k + 1) as i32)];
                    if clauses.get(idx) != Some(&want) { return None; }
                    idx += 1;
                }
            }
        }
    }
    Some(CnfShape::RoundRobin { n_teams: n, n_days: d })
}

// ─── Proof emission ────────────────────────────────────────────────────────

/// Emit a VeriPB-format polynomial proof for the given shape into `w`.
/// Returns an error if the shape is `Unknown`.
pub fn emit_proof<W: Write>(
    shape: &CnfShape,
    n_clauses: usize,
    w: &mut W,
) -> io::Result<()> {
    match shape {
        CnfShape::Php { n, m } => emit_php(*n, *m, n_clauses, w),
        CnfShape::RoundRobin { n_teams, n_days } => {
            emit_roundrobin(*n_teams, *n_days, n_clauses, w)
        }
        CnfShape::EmbeddedPigeonhole(ep) => {
            emit_embedded_pigeonhole(ep, n_clauses, w)
        }
        CnfShape::Unknown => Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "cannot emit Cook proof for Unknown shape",
        )),
    }
}

// ─── PHP emitter ────────────────────────────────────────────────────────────
//
// Cook 1976 PHP construction.  See `tools/cook_php_proof.py` for the
// reference Python implementation we're porting.

/// One reduction layer's tracking state.  Variable names + ConstraintIDs
/// for derived pigeon and mutex clauses.
struct PhpLayer {
    n_pigeons: usize,
    n_holes: usize,
    /// Build the layer's variable name for pigeon i (1-indexed) hole j (1-indexed).
    name: Box<dyn Fn(usize, usize) -> String>,
    /// Pigeon clause ConstraintID, one per pigeon.
    pigeon: Vec<usize>,                 // pigeon[i-1] = ID of pigeon i's clause
    /// Mutex ConstraintID for pigeons (i, j) at hole k.  Keys: (min(i,j), max(i,j), k).
    mutex: std::collections::HashMap<(usize, usize, usize), usize>,
}

fn emit_php<W: Write>(n: usize, m: usize, n_clauses: usize, w: &mut W) -> io::Result<()> {
    assert!(n > m && m >= 2, "PHP-{}-{} not UNSAT or out of range", n, m);
    writeln!(w, "pseudo-Boolean proof version 3.0")?;
    writeln!(w, "% Cook 1976 PHP-{}-{} via extension variables.", n, m)?;
    writeln!(w, "f {};", n_clauses)?;
    writeln!(w)?;

    let mut cur = n_clauses;

    // Layer 0: original CNF.
    let m0 = m;
    let mut layer = PhpLayer {
        n_pigeons: n,
        n_holes: m,
        name: Box::new(move |i, j| format!("x{}", (i - 1) * m0 + j)),
        pigeon: (1..=n).collect(),
        mutex: {
            let mut h = std::collections::HashMap::new();
            // Mutex layout in CNF: for each hole k, for each (i, j) with i<j, lex.
            let n_pigeon_clauses = n;
            let mut idx = n_pigeon_clauses;
            for k in 1..=m {
                for i in 1..=n {
                    for j in (i + 1)..=n {
                        idx += 1;
                        h.insert((i, j, k), idx);
                    }
                }
            }
            h
        },
    };

    // Apply M-2 Cook reductions until we hit PHP-(n-m+2)-2.
    let mut layer_idx = 0;
    while layer.n_holes > 2 {
        layer_idx += 1;
        let (new_layer, new_cur) = emit_layer_reduction(&layer, layer_idx, cur, w)?;
        cur = new_cur;
        layer = new_layer;
    }

    // Closure step.
    cur = emit_closure(&layer, cur, w)?;
    let _ = cur;

    writeln!(w, "rup >= 1 ;")?;
    writeln!(w, "output NONE;")?;
    writeln!(w, "conclusion UNSAT : -1;")?;
    writeln!(w, "end pseudo-Boolean proof;")?;
    Ok(())
}

fn emit_layer_reduction<W: Write>(
    inp: &PhpLayer,
    layer_idx: usize,
    mut cur: usize,
    w: &mut W,
) -> io::Result<(PhpLayer, usize)> {
    let n = inp.n_pigeons;
    let m = inp.n_holes;
    assert!(n > m, "layer reduction needs n > m; got n={} m={}", n, m);
    let new_n = n - 1;
    let new_m = m - 1;
    let p = |i, j| (inp.name)(i, j);
    let n_p = |i, j| format!("~{}", (inp.name)(i, j));
    let q_name = move |i: usize, j: usize| format!("Q{}_{}_{}", layer_idx, i, j);
    let q_name_box: Box<dyn Fn(usize, usize) -> String> =
        Box::new(move |i, j| format!("Q{}_{}_{}", layer_idx, i, j));

    writeln!(w, "% === Layer {}: reduce PHP-{}-{} → PHP-{}-{} ===",
             layer_idx, n, m, new_n, new_m)?;

    // Step 1: introduce Q vars via 4 reds each.
    let mut q_id: std::collections::HashMap<(usize, usize), usize> = Default::default();
    for i in 1..n {
        for j in 1..m {
            let q = q_name(i, j);
            let nq = format!("~{}", q);
            writeln!(w, "% Define {} = P_{{{},{}}} ∨ (P_{{{},{}}} ∧ P_{{{},{}}})",
                     q, i, j, i, m, n, j)?;
            writeln!(w, "red 1 {} 1 {} >= 1 : {} -> 1 ;", q, n_p(i, j), q)?;
            writeln!(w, "red 1 {} 1 {} 1 {} >= 1 : {} -> 1 ;",
                     q, n_p(i, m), n_p(n, j), q)?;
            writeln!(w, "red 1 {} 1 {} 1 {} >= 1 : {} -> 0 ;",
                     nq, p(i, j), p(i, m), q)?;
            writeln!(w, "red 1 {} 1 {} 1 {} >= 1 : {} -> 0 ;",
                     nq, p(i, j), p(n, j), q)?;
            q_id.insert((i, j), cur + 1);
            cur += 4;
        }
    }

    // Step 2: derive Q-pigeon clauses (3M pol steps per pigeon, see walkthrough).
    let mut new_pigeon = vec![0usize; new_n];
    let pigeon_n = inp.pigeon[n - 1];
    for i in 1..n {
        let pig_i = inp.pigeon[i - 1];
        let mut_i_n_m = *inp.mutex.get(&(i.min(n), i.max(n), m)).expect("mut(i, n, m)");
        writeln!(w, "% Q-pigeon clause for pigeon {} (layer {}).", i, layer_idx)?;
        // E = pigeon_i + mutex(i, n, m)
        writeln!(w, "pol {} {} + s ;", pig_i, mut_i_n_m)?;
        cur += 1;
        let mut prev = cur;
        // F = E + pigeon_n
        writeln!(w, "pol {} {} + s ;", prev, pigeon_n)?;
        cur += 1; prev = cur;
        // G_k = prev + C1_{i,k} for k=1..m-1
        for k in 1..m {
            let c1 = *q_id.get(&(i, k)).unwrap();
            writeln!(w, "pol {} {} + s ;", prev, c1)?;
            cur += 1; prev = cur;
        }
        // I_k = prev + C2_{i,k}
        for k in 1..m {
            let c2 = q_id[&(i, k)] + 1;
            writeln!(w, "pol {} {} + s ;", prev, c2)?;
            cur += 1; prev = cur;
        }
        // K = prev + pigeon_i
        writeln!(w, "pol {} {} + s ;", prev, pig_i)?;
        cur += 1; prev = cur;
        // L_k = prev + C1_{i,k}
        for k in 1..m {
            let c1 = q_id[&(i, k)];
            writeln!(w, "pol {} {} + s ;", prev, c1)?;
            cur += 1; prev = cur;
        }
        new_pigeon[i - 1] = prev;
    }

    // Step 3: Q-mutex clauses (7 pol per).  Case split on P_{n,k}.
    let mut new_mutex: std::collections::HashMap<(usize, usize, usize), usize> = Default::default();
    for k in 1..m {
        for i in 1..(n - 1) {
            for j in (i + 1)..n {
                let c3_i = q_id[&(i, k)] + 2;
                let c4_i = q_id[&(i, k)] + 3;
                let c3_j = q_id[&(j, k)] + 2;
                let c4_j = q_id[&(j, k)] + 3;
                let mut_ij_k = inp.mutex[&(i, j, k)];
                let mut_ij_m = inp.mutex[&(i, j, m)];
                let mut_in_k = *inp.mutex.get(&(i.min(n), i.max(n), k))
                    .or_else(|| inp.mutex.get(&(n.min(i), n.max(i), k))).unwrap();
                let mut_jn_k = *inp.mutex.get(&(j.min(n), j.max(n), k))
                    .or_else(|| inp.mutex.get(&(n.min(j), n.max(j), k))).unwrap();
                writeln!(w, "% Q-mutex ~Q_{{{},{}}} + ~Q_{{{},{}}} (7 pol).",
                         i, k, j, k)?;
                // Case 1 (2 pol)
                writeln!(w, "pol {} {} + s ;", c4_i, mut_ij_k)?; cur += 1; let r1 = cur;
                writeln!(w, "pol {} {} + s ;", r1, c4_j)?; cur += 1; let case1 = cur;
                // Case 2 (4 pol)
                writeln!(w, "pol {} {} + s ;", c3_i, mut_in_k)?; cur += 1; let sg = cur;
                writeln!(w, "pol {} {} + s ;", sg, mut_ij_m)?; cur += 1; let sp = cur;
                writeln!(w, "pol {} {} + s ;", sp, c3_j)?; cur += 1; let spp = cur;
                writeln!(w, "pol {} {} + s ;", spp, mut_jn_k)?; cur += 1; let case2 = cur;
                // Combine
                writeln!(w, "pol {} {} + s ;", case1, case2)?; cur += 1;
                new_mutex.insert((i, j, k), cur);
            }
        }
    }
    writeln!(w)?;

    let new_layer = PhpLayer {
        n_pigeons: new_n,
        n_holes: new_m,
        name: q_name_box,
        pigeon: new_pigeon,
        mutex: new_mutex,
    };
    Ok((new_layer, cur))
}

fn emit_closure<W: Write>(
    layer: &PhpLayer,
    mut cur: usize,
    w: &mut W,
) -> io::Result<usize> {
    let k = layer.n_pigeons;
    let m = layer.n_holes;
    if m == 2 && k >= 3 {
        // Cyclic-pigeon-swap red.  Cycle BOTH P-vars and Q-row vars.
        // (Only the current layer's vars need cycling since earlier
        // layers' P vars are no longer referenced.)
        writeln!(w, "% Closure: PHP-{}-{} via cyclic-pigeon red.", k, m)?;
        let mut sub = Vec::new();
        for src in 1..=k {
            let dst = if src == k { 1 } else { src + 1 };
            for h in 1..=m {
                sub.push(format!("{} -> {}", (layer.name)(src, h), (layer.name)(dst, h)));
            }
        }
        writeln!(w, "red 1 {} >= 1 : {} ;", (layer.name)(1, 1), sub.join(" "))?;
        cur += 1;
        Ok(cur)
    } else if m == 1 {
        writeln!(w, "% Closure: PHP-{}-1 (K pigeons in 1 hole) trivially UNSAT.", k)?;
        Ok(cur)
    } else {
        panic!("closure for PHP-{}-{} not implemented", k, m)
    }
}

// ─── RoundRobin emitter ────────────────────────────────────────────────────

fn emit_roundrobin<W: Write>(
    n: usize, d: usize, n_clauses: usize, w: &mut W,
) -> io::Result<()> {
    assert!(n >= 2 && d >= 1);
    let n_pairs = n * (n - 1) / 2;
    let capacity = d * n / 2;
    assert!(n_pairs > capacity, "RR n={} d={} not UNSAT", n, d);
    let var = |pair_idx: usize, day_idx: usize| -> usize {
        pair_idx * d + day_idx + 1
    };
    let pairs: Vec<(usize, usize)> = (0..n)
        .flat_map(|i| ((i + 1)..n).map(move |j| (i, j)))
        .collect();

    // CNF clause IDs (we know the layout matches official benchmark).
    // Per-pair block: 1 pigeon + C(d,2) pair-day mutex.
    let pair_block = 1 + d * (d - 1) / 2;
    // pigeon_id(p) = 1 + p * pair_block  (1-indexed CNF clause ID).
    let pigeon_id = |p: usize| 1 + p * pair_block;
    // team_day_mutex base: after all n_pairs pair-blocks.
    let team_base = n_pairs * pair_block;
    // For (team t, day k), the C(K, 2) mutex clauses start at:
    //   team_base + (cumulative offset for prior (t, k))
    //   where each (t, k) has C(K, 2) clauses, K = n-1.
    let k_team = n - 1;  // matches per team
    let c_k_2 = k_team * (k_team - 1) / 2;
    let team_day_block = c_k_2;
    // team_day_mutex_id(t, k, pair_i, pair_j) requires the (pair_i, pair_j)
    // index within the (t, k) block.  Inside each (t, k), pairs are listed
    // as: for i in 0..K, for j in (i+1)..K → C(K,2) entries.
    let matches_of_team: Vec<Vec<usize>> = (0..n)
        .map(|t| {
            let mut m: Vec<usize> = (0..n_pairs)
                .filter(|&pi| { let (a, b) = pairs[pi]; a == t || b == t })
                .collect();
            m.sort();
            m
        })
        .collect();
    let team_day_mutex_id = |t: usize, k: usize, pi: usize, pj: usize| -> usize {
        let m = &matches_of_team[t];
        let i = m.iter().position(|&x| x == pi).expect("pi in team");
        let j = m.iter().position(|&x| x == pj).expect("pj in team");
        let (i, j) = if i < j { (i, j) } else { (j, i) };
        // Index within the (t, k) block:
        //   for ii in 0..K, for jj in (ii+1)..K → linearised
        // Linear pos of (i, j) = sum_{ii<i} (K - 1 - ii) + (j - i - 1)
        let mut pos = 0;
        for ii in 0..i { pos += k_team - 1 - ii; }
        pos += j - i - 1;
        // Total (t, k) offset within the team_day block:
        let block_offset = t * d * team_day_block + k * team_day_block;
        team_base + block_offset + pos + 1
    };

    writeln!(w, "pseudo-Boolean proof version 3.0")?;
    writeln!(w, "% RoundRobin n={} d={}: {} matches > {} slots.",
             n, d, n_pairs, capacity)?;
    writeln!(w, "f {};", n_clauses)?;
    writeln!(w)?;

    let mut cur = n_clauses;

    // Step 1: per (team, day) at-most-1 via recursive-red subroutine.
    let mut team_day_amo_id: std::collections::HashMap<(usize, usize), usize> = Default::default();
    writeln!(w, "% --- Step 1: per (team, day) at-most-1 ({} = n-1 matches per team) ---",
             k_team)?;
    if k_team < 2 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "n_teams < 3 has no team-day mutex; cannot apply Cook subroutine",
        ));
    }
    for t in 0..n {
        let mt = &matches_of_team[t];
        for k in 0..d {
            let mvars: Vec<String> = mt.iter().map(|&p| format!("x{}", var(p, k))).collect();
            if k_team == 2 {
                // IH(2) = the single binary mutex itself.
                let amo = team_day_mutex_id(t, k, mt[0], mt[1]);
                team_day_amo_id.insert((t, k), amo);
                continue;
            }
            // IH(3) base: pol of 3 mutex / 2.
            let m01 = team_day_mutex_id(t, k, mt[0], mt[1]);
            let m02 = team_day_mutex_id(t, k, mt[0], mt[2]);
            let m12 = team_day_mutex_id(t, k, mt[1], mt[2]);
            writeln!(w, "% IH(3) for team {} day {}: at-most-1 of {}, {}, {}.",
                     t, k, mvars[0], mvars[1], mvars[2])?;
            writeln!(w, "pol {} {} + {} + 2 d ;", m01, m02, m12)?;
            cur += 1;
            let mut current_ih = cur;
            // IH(k) for k = 4..=K via recursive red.
            for kk in 4..=k_team {
                let lits: Vec<String> = (0..kk)
                    .map(|i| format!("+1 ~{}", mvars[i])).collect();
                writeln!(w, "red {} >= {} : {} -> 0 ;",
                         lits.join(" "), kk - 1, mvars[kk - 1])?;
                cur += 1;
                current_ih = cur;
            }
            team_day_amo_id.insert((t, k), current_ih);
        }
    }
    writeln!(w)?;
    let _ = current_ih_stub();   // (silence "unused" if any path)

    // Step 2: per day at-most-n/2 = sum of n team-amo's / 2.
    let mut per_day_amo: Vec<usize> = vec![0; d];
    writeln!(w, "% --- Step 2: per day at-most-{} (= n/2 matches) ---", n / 2)?;
    for k in 0..d {
        let team_ids: Vec<usize> = (0..n).map(|t| team_day_amo_id[&(t, k)]).collect();
        let mut expr = team_ids[0].to_string();
        for tid in &team_ids[1..] { expr += &format!(" {} +", tid); }
        expr += " 2 d";
        writeln!(w, "pol {} ;", expr)?;
        cur += 1;
        per_day_amo[k] = cur;
    }
    writeln!(w)?;

    // Step 3: total at-most-(d * n/2) = sum per_day.
    writeln!(w, "% --- Step 3: sum per-day at-most → total at-most ---")?;
    let mut expr = per_day_amo[0].to_string();
    for k in 1..d { expr += &format!(" {} +", per_day_amo[k]); }
    writeln!(w, "pol {} ;", expr)?;
    cur += 1;
    let total_amo = cur;
    writeln!(w)?;

    // Step 4: pigeon-sum at-least-n_pairs.
    writeln!(w, "% --- Step 4: sum pigeon clauses → at-least-n_pairs ---")?;
    let mut expr = pigeon_id(0).to_string();
    for p in 1..n_pairs { expr += &format!(" {} +", pigeon_id(p)); }
    writeln!(w, "pol {} ;", expr)?;
    cur += 1;
    let pigeon_sum = cur;
    writeln!(w)?;

    // Step 5: contradiction.
    writeln!(w, "% --- Step 5: combine → contradiction ---")?;
    writeln!(w, "pol {} {} + ;", total_amo, pigeon_sum)?;
    cur += 1;
    writeln!(w, "rup >= 1 ;")?;
    writeln!(w)?;
    writeln!(w, "output NONE;")?;
    writeln!(w, "conclusion UNSAT : -1;")?;
    writeln!(w, "end pseudo-Boolean proof;")?;
    let _ = cur;
    Ok(())
}

// Helper that does nothing — placeholder so that an unused-variable
// path warning doesn't surface when `kk` loops zero times.
fn current_ih_stub() -> usize { 0 }

// ─── Embedded-pigeonhole emitter (generic cardinality + mutex) ──────────────
//
// Generalises PHP/RoundRobin to ANY CNF carrying an embedded pigeonhole,
// including reshuffled / polarity-flipped encodings (e.g. harder-fphp):
// P variable-disjoint at-least-one "pigeon" clauses of equal arity S, with
// literals of ANY polarity, where each "hole" (the P pigeon-literals for
// one slot) forms a COMPLETE pairwise-mutex clique (holds <= 1).  P > S =>
// UNSAT.  Holes are recovered two ways (tried in order):
//   (A) component: connected components of the cross-pigeon mutex graph
//                  (PHP / reshuffled fphp);
//   (B) aligned:   the s-th literal of each pigeon sorted by |var|
//                  (MVRoundRobin, whose team-capacity mutexes merge the
//                  component graph).
// The proof is emitted at the LITERAL level so flipped polarities work
// transparently.  Detected from raw clause structure (no hand-coded family
// knowledge).  Port of `tools/cook_card_proof.py`.

/// Extracted embedded-pigeonhole structure (see [`detect_embedded_pigeonhole`]).
/// Carries clause ids + signed slot literals because, unlike PHP/RoundRobin,
/// the variable layout is read out of the input CNF (and may be flipped).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EmbeddedPigeonhole {
    /// 1-based CNF clause id of each pigeon's at-least-one clause.
    pub pigeon_ids: Vec<usize>,
    /// holes[s] = the P pigeon-LITERALS forming hole s (in pigeon order).
    pub holes: Vec<Vec<i32>>,
    /// 1-based clause id of the binary clause EXCLUDING the literal pair
    /// (la, lb) — i.e. the mutex `~la v ~lb`.  Keyed (min, max).
    pub mutex_ids: std::collections::HashMap<(i32, i32), usize>,
}

/// Try to recognise an embedded pigeonhole.  Pigeons = variable-disjoint
/// at-least-one clauses (ANY polarity) of arity >= 3, all sharing the
/// first such arity seen.  Holes are recovered by [`recover_component`]
/// (cross-pigeon mutex components) and, failing that, [`recover_aligned`]
/// (s-th literal of each pigeon).  Each hole must be a COMPLETE P-clique;
/// requires P > S.  Returns `None` if the structure is absent — so
/// emission only ever fires on a confirmed pigeonhole, with every
/// referenced mutex present (sound by construction).
pub fn detect_embedded_pigeonhole(
    clauses: &[Vec<i32>],
    _nvars: usize,
) -> Option<EmbeddedPigeonhole> {
    use std::collections::{HashMap, HashSet};
    // Pigeons: disjoint clauses of the first arity (>= 3) seen.
    let mut arity = 0usize;
    let mut pigeons: Vec<Vec<i32>> = Vec::new();
    let mut pigeon_ids: Vec<usize> = Vec::new();
    for (i, c) in clauses.iter().enumerate() {
        if c.len() >= 2 {
            if arity == 0 && c.len() >= 3 {
                arity = c.len();
            }
            if arity != 0 && c.len() == arity {
                pigeons.push(c.clone());
                pigeon_ids.push(i + 1);
            }
        }
    }
    let p = pigeons.len();
    let s = arity;
    if p < 3 || s < 2 || p <= s {
        return None;
    }
    // Variable-disjoint (by |var|) + literal -> pigeon map.
    let mut seen: HashSet<i32> = HashSet::new();
    let mut lit2pig: HashMap<i32, usize> = HashMap::new();
    for (pi, g) in pigeons.iter().enumerate() {
        for &l in g {
            if !seen.insert(l.abs()) {
                return None;
            }
            lit2pig.insert(l, pi);
        }
    }
    // Binary mutex index keyed on the EXCLUDED literal pair (~la v ~lb).
    let mut mutex_ids: HashMap<(i32, i32), usize> = HashMap::new();
    for (i, c) in clauses.iter().enumerate() {
        if c.len() == 2 {
            let la = -c[0];
            let lb = -c[1];
            let key = if la < lb { (la, lb) } else { (lb, la) };
            mutex_ids.entry(key).or_insert(i + 1);
        }
    }
    let holes = recover_component(&pigeons, &lit2pig, &mutex_ids)
        .or_else(|| recover_aligned(&pigeons, &mutex_ids))?;
    if holes.is_empty() || p <= holes.len() {
        return None;
    }
    Some(EmbeddedPigeonhole { pigeon_ids, holes, mutex_ids })
}

/// Holes = connected components of the cross-pigeon mutex graph; each must
/// be a complete P-clique with one literal per pigeon.  Seeds from pigeon
/// 0's literals (one per hole) for a deterministic hole order.  Handles
/// PHP and reshuffled/flipped fphp.
fn recover_component(
    pigeons: &[Vec<i32>],
    lit2pig: &std::collections::HashMap<i32, usize>,
    mutex_ids: &std::collections::HashMap<(i32, i32), usize>,
) -> Option<Vec<Vec<i32>>> {
    use std::collections::{HashMap, HashSet};
    let p = pigeons.len();
    let mut adj: HashMap<i32, HashSet<i32>> = HashMap::new();
    for &(la, lb) in mutex_ids.keys() {
        if let (Some(&pa), Some(&pb)) = (lit2pig.get(&la), lit2pig.get(&lb)) {
            if pa != pb {
                adj.entry(la).or_default().insert(lb);
                adj.entry(lb).or_default().insert(la);
            }
        }
    }
    let mut seen: HashSet<i32> = HashSet::new();
    let mut holes: Vec<Vec<i32>> = Vec::new();
    for &seed in &pigeons[0] {
        if seen.contains(&seed) {
            continue;
        }
        let mut stack = vec![seed];
        let mut comp: Vec<i32> = Vec::new();
        while let Some(u) = stack.pop() {
            if !seen.insert(u) {
                continue;
            }
            comp.push(u);
            if let Some(ns) = adj.get(&u) {
                for &v in ns {
                    if !seen.contains(&v) {
                        stack.push(v);
                    }
                }
            }
        }
        if comp.len() != p {
            return None;
        }
        let pigset: HashSet<usize> = comp.iter().map(|l| lit2pig[l]).collect();
        if pigset.len() != p {
            return None;
        }
        for i in 0..comp.len() {
            for j in (i + 1)..comp.len() {
                if !adj.get(&comp[i]).map_or(false, |ns| ns.contains(&comp[j])) {
                    return None;
                }
            }
        }
        comp.sort_by_key(|l| lit2pig[l]);
        holes.push(comp);
    }
    // Every pigeon literal must be covered by some hole.
    if seen.len() != p * pigeons[0].len() {
        return None;
    }
    Some(holes)
}

/// Holes = the s-th literal of each pigeon (sorted by |var|); each slot
/// must be a complete pairwise-mutex clique.  Handles MVRoundRobin (whose
/// team-capacity mutexes merge the component graph, so it needs this
/// positional method instead).
fn recover_aligned(
    pigeons: &[Vec<i32>],
    mutex_ids: &std::collections::HashMap<(i32, i32), usize>,
) -> Option<Vec<Vec<i32>>> {
    let p = pigeons.len();
    let s = pigeons[0].len();
    let pigs: Vec<Vec<i32>> = pigeons
        .iter()
        .map(|g| {
            let mut v = g.clone();
            v.sort_by_key(|l| l.abs());
            v
        })
        .collect();
    let mut holes: Vec<Vec<i32>> = Vec::with_capacity(s);
    for slot in 0..s {
        let hv: Vec<i32> = (0..p).map(|pp| pigs[pp][slot]).collect();
        for i in 0..p {
            for j in (i + 1)..p {
                let key = if hv[i] < hv[j] { (hv[i], hv[j]) } else { (hv[j], hv[i]) };
                if !mutex_ids.contains_key(&key) {
                    return None;
                }
            }
        }
        holes.push(hv);
    }
    Some(holes)
}

/// VeriPB term for `~l` (the literal being false): `~x{v}` if l>0 else `x{v}`.
fn neg_lit(l: i32) -> String {
    if l > 0 { format!("~x{}", l) } else { format!("x{}", -l) }
}

/// Emit the Cook cardinality proof for an embedded pigeonhole, at the
/// LITERAL level (so polarity-flipped encodings work transparently).  Per
/// hole, derive at-most-1 over its P literals via the recursive Cook
/// subroutine (base IH(3) = `pol` of 3 mutexes / 2; IH(k) = `red` on the
/// witness var -> {0,1}), sum the S holes (Sum ~l >= S*(P-1)) against the
/// P pigeon clauses (Sum l >= P), and combine: l + ~l = P*S over all P*S
/// literals, so P*S >= S*(P-1) + P = P*S + (P-S) forces 0 >= P-S -> ⊥.
fn emit_embedded_pigeonhole<W: Write>(
    ep: &EmbeddedPigeonhole,
    n_clauses: usize,
    w: &mut W,
) -> io::Result<()> {
    let p = ep.pigeon_ids.len();
    let s = ep.holes.len();
    assert!(p > s && p >= 3, "embedded pigeonhole needs P > S, P >= 3");
    let key = |a: i32, b: i32| if a < b { (a, b) } else { (b, a) };

    writeln!(w, "pseudo-Boolean proof version 3.0")?;
    writeln!(w, "% embedded pigeonhole: {} pigeons > {} holes (literal-level Cook)", p, s)?;
    writeln!(w, "f {};", n_clauses)?;
    writeln!(w)?;
    let mut cur = n_clauses;

    // Step 1: per-hole at-most-1 over the P pigeon-literals.
    writeln!(w, "% --- Step 1: per-hole at-most-1 over {} literals (recursive Cook) ---", p)?;
    let mut hole_amo: Vec<usize> = Vec::with_capacity(s);
    for hv in &ep.holes {
        let m01 = ep.mutex_ids[&key(hv[0], hv[1])];
        let m02 = ep.mutex_ids[&key(hv[0], hv[2])];
        let m12 = ep.mutex_ids[&key(hv[1], hv[2])];
        writeln!(w, "pol {} {} + {} + 2 d ;", m01, m02, m12)?;
        cur += 1;
        let mut current = cur;
        for k in 4..=p {
            let lits: Vec<String> =
                (0..k).map(|i| format!("+1 {}", neg_lit(hv[i]))).collect();
            let wl = hv[k - 1];
            writeln!(w, "red {} >= {} : x{} -> {} ;",
                     lits.join(" "), k - 1, wl.abs(), if wl > 0 { 0 } else { 1 })?;
            cur += 1;
            current = cur;
        }
        hole_amo.push(current);
    }
    writeln!(w)?;

    // Step 2: sum the S hole at-most-1's -> Sum ~x >= S*(P-1).
    writeln!(w, "% --- Step 2: sum hole at-most-1's ---")?;
    let mut expr = hole_amo[0].to_string();
    for h in &hole_amo[1..] {
        expr += &format!(" {} +", h);
    }
    writeln!(w, "pol {} ;", expr)?;
    cur += 1;
    let amo_sum = cur;
    writeln!(w)?;

    // Step 3: sum the P pigeon at-least-one clauses -> Sum x >= P.
    writeln!(w, "% --- Step 3: sum pigeon at-least-one clauses ---")?;
    let mut expr = ep.pigeon_ids[0].to_string();
    for &pid in &ep.pigeon_ids[1..] {
        expr += &format!(" {} +", pid);
    }
    writeln!(w, "pol {} ;", expr)?;
    cur += 1;
    let pigeon_sum = cur;
    writeln!(w)?;

    // Step 4: combine -> contradiction.
    writeln!(w, "% --- Step 4: combine -> contradiction ---")?;
    writeln!(w, "pol {} {} + ;", amo_sum, pigeon_sum)?;
    cur += 1;
    writeln!(w, "rup >= 1 ;")?;
    writeln!(w)?;
    writeln!(w, "output NONE;")?;
    writeln!(w, "conclusion UNSAT : -1;")?;
    writeln!(w, "end pseudo-Boolean proof;")?;
    let _ = cur;
    Ok(())
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn php_cnf(n: usize, m: usize) -> Vec<Vec<i32>> {
        let var = |i: usize, j: usize| -> i32 { ((i - 1) * m + j) as i32 };
        let mut cs = Vec::new();
        for i in 1..=n {
            cs.push((1..=m).map(|j| var(i, j)).collect());
        }
        for k in 1..=m {
            for i in 1..=n {
                for j in (i + 1)..=n {
                    cs.push(vec![-var(i, k), -var(j, k)]);
                }
            }
        }
        cs
    }

    fn rr_cnf(n: usize, d: usize) -> Vec<Vec<i32>> {
        let pairs: Vec<(usize, usize)> = (0..n)
            .flat_map(|i| ((i + 1)..n).map(move |j| (i, j))).collect();
        let n_pairs = pairs.len();
        let var = |p: usize, k: usize| -> i32 { (p * d + k + 1) as i32 };
        let mut cs = Vec::new();
        for p in 0..n_pairs {
            cs.push((0..d).map(|k| var(p, k)).collect());
            for k1 in 0..d {
                for k2 in (k1 + 1)..d {
                    cs.push(vec![-var(p, k1), -var(p, k2)]);
                }
            }
        }
        for t in 0..n {
            let mut m: Vec<usize> = (0..n_pairs)
                .filter(|&pi| { let (a, b) = pairs[pi]; a == t || b == t })
                .collect();
            m.sort();
            for k in 0..d {
                for i in 0..m.len() {
                    for j in (i + 1)..m.len() {
                        cs.push(vec![-var(m[i], k), -var(m[j], k)]);
                    }
                }
            }
        }
        cs
    }

    #[test]
    fn detect_php_4_3() {
        let cnf = php_cnf(4, 3);
        let nv = 4 * 3;
        assert_eq!(detect_shape(&cnf, nv), CnfShape::Php { n: 4, m: 3 });
    }

    #[test]
    fn detect_php_20_19() {
        let cnf = php_cnf(20, 19);
        let nv = 20 * 19;
        assert_eq!(detect_shape(&cnf, nv), CnfShape::Php { n: 20, m: 19 });
    }

    #[test]
    fn detect_rr_n16_d13() {
        let cnf = rr_cnf(16, 13);
        let nv = 16 * 15 / 2 * 13;
        assert_eq!(detect_shape(&cnf, nv), CnfShape::RoundRobin { n_teams: 16, n_days: 13 });
    }

    #[test]
    fn exactly_one_csp_detects_php_and_rr() {
        // PHP and RoundRobin are exactly-one CSPs: disjoint at-least-one
        // pigeon clauses + binary at-most-one mutexes.
        assert!(is_exactly_one_csp(&php_cnf(4, 3)));
        assert!(is_exactly_one_csp(&rr_cnf(8, 5)));
    }

    #[test]
    fn exactly_one_csp_rejects_arithmetic_and_overlap() {
        // Mixed-polarity XOR clauses (no all-positive at-least-one) —
        // must keep the VSIDS portfolio, not route to EffectiveCount.
        let xor = vec![
            vec![1, 2, -3], vec![1, -2, 3], vec![-1, 2, 3], vec![-1, -2, -3],
            vec![4, 5, -6], vec![4, -5, 6], vec![-4, 5, 6], vec![-4, -5, -6],
        ];
        assert!(!is_exactly_one_csp(&xor));
        // At-least-one clauses that share a variable aren't a partition.
        let overlap = vec![vec![1, 2, 3], vec![3, 4, 5], vec![-1, -2]];
        assert!(!is_exactly_one_csp(&overlap));
    }

    #[test]
    fn detect_unknown_random() {
        let cnf = vec![vec![1, 2, 3], vec![-1, -2], vec![3, -4]];
        assert_eq!(detect_shape(&cnf, 4), CnfShape::Unknown);
    }

    #[test]
    fn emit_php_4_3_produces_output() {
        let cnf = php_cnf(4, 3);
        let shape = detect_shape(&cnf, 12);
        let mut buf = Vec::new();
        emit_proof(&shape, cnf.len(), &mut buf).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.starts_with("pseudo-Boolean proof version 3.0"));
        assert!(s.contains("end pseudo-Boolean proof;"));
        // Sanity: should have at least n*M Q-defn reds (4 per Q).
        let n_red = s.lines().filter(|l| l.starts_with("red ")).count();
        assert!(n_red >= 24);   // 3*2 Q vars * 4 reds = 24
    }

    #[test]
    fn emit_rr_n4_d2_produces_output() {
        let cnf = rr_cnf(4, 2);
        let nv = 4 * 3 / 2 * 2;
        let shape = detect_shape(&cnf, nv);
        let mut buf = Vec::new();
        emit_proof(&shape, cnf.len(), &mut buf).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("RoundRobin n=4 d=2"));
        assert!(s.ends_with("end pseudo-Boolean proof;\n"));
    }

    /// PHP-P-S with NON-canonical variable numbering (stride 10) — so the
    /// byte-exact `detect_php` misses it and the generic embedded-
    /// pigeonhole detector must catch it instead.  pigeon i, slot j -> var
    /// `i*10 + j + 1`; per-slot complete mutex cliques.
    fn embedded_php_cnf(p: usize, s: usize) -> Vec<Vec<i32>> {
        let var = |i: usize, j: usize| (i * 10 + j + 1) as i32;
        let mut cs = Vec::new();
        for i in 0..p {
            cs.push((0..s).map(|j| var(i, j)).collect());
        }
        for j in 0..s {
            for i1 in 0..p {
                for i2 in (i1 + 1)..p {
                    cs.push(vec![-var(i1, j), -var(i2, j)]);
                }
            }
        }
        cs
    }

    #[test]
    fn detect_embedded_pigeonhole_non_canonical() {
        let cnf = embedded_php_cnf(4, 3); // 4 pigeons > 3 holes
        let shape = detect_shape(&cnf, 3 * 10 + 3);
        match &shape {
            CnfShape::EmbeddedPigeonhole(ep) => {
                assert_eq!(ep.pigeon_ids.len(), 4);
                assert_eq!(ep.holes.len(), 3);
                // every slot clique must be complete (all C(4,2)=6 mutexes)
                assert_eq!(ep.mutex_ids.len(), 3 * 6);
            }
            other => panic!("expected EmbeddedPigeonhole, got {:?}", other),
        }
    }

    #[test]
    fn emit_embedded_pigeonhole_produces_output() {
        let cnf = embedded_php_cnf(5, 3);
        let shape = detect_shape(&cnf, 4 * 10 + 3);
        let mut buf = Vec::new();
        emit_proof(&shape, cnf.len(), &mut buf).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.starts_with("pseudo-Boolean proof version 3.0"));
        assert!(s.contains("embedded pigeonhole: 5 pigeons > 3 holes"));
        assert!(s.ends_with("end pseudo-Boolean proof;\n"));
        // 3 holes, each IH(3) base + IH(4),IH(5) recursive red = 2 reds/hole.
        let n_red = s.lines().filter(|l| l.starts_with("red ")).count();
        assert_eq!(n_red, 3 * 2);
    }

    #[test]
    fn embedded_pigeonhole_rejects_sat_ratio() {
        // P <= S (4 pigeons, 4 holes) is satisfiable — must NOT detect.
        let cnf = embedded_php_cnf(4, 4);
        assert_eq!(detect_shape(&cnf, 3 * 10 + 4), CnfShape::Unknown);
    }

    /// Embedded PHP with FLIPPED polarities (some literals negated, like a
    /// reshuffled fphp) — exercises the literal-level + component-recovery
    /// path.  Holes are NOT positionally aligned with respect to polarity,
    /// so this only detects if the cross-pigeon component recovery works.
    fn embedded_php_cnf_flipped(p: usize, s: usize) -> Vec<Vec<i32>> {
        let lit = |i: usize, j: usize| {
            let v = (i * 10 + j + 1) as i32;
            if (i + j) % 2 == 1 { -v } else { v }
        };
        let mut cs = Vec::new();
        for i in 0..p {
            cs.push((0..s).map(|j| lit(i, j)).collect());
        }
        for j in 0..s {
            for i1 in 0..p {
                for i2 in (i1 + 1)..p {
                    cs.push(vec![-lit(i1, j), -lit(i2, j)]);
                }
            }
        }
        cs
    }

    #[test]
    fn detect_and_emit_flipped_embedded_pigeonhole() {
        let cnf = embedded_php_cnf_flipped(5, 3); // 5 pigeons > 3 holes
        let shape = detect_shape(&cnf, 4 * 10 + 3);
        match &shape {
            CnfShape::EmbeddedPigeonhole(ep) => {
                assert_eq!(ep.pigeon_ids.len(), 5);
                assert_eq!(ep.holes.len(), 3);
                // at least one hole literal must be negative (flipped).
                assert!(ep.holes.iter().flatten().any(|&l| l < 0));
            }
            other => panic!("expected EmbeddedPigeonhole, got {:?}", other),
        }
        let mut buf = Vec::new();
        emit_proof(&shape, cnf.len(), &mut buf).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.contains("embedded pigeonhole: 5 pigeons > 3 holes"));
        assert!(s.ends_with("end pseudo-Boolean proof;\n"));
    }
}
