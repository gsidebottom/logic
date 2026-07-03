//! Certified parity UNSAT: VeriPB proofs for GF(2) Gaussian-elimination
//! refutations, after Gocht & Nordström, "Certifying Parity Reasoning
//! Efficiently Using Pseudo-Boolean Proofs" (AAAI'21 / JAIR).
//!
//! STANDALONE prover in the cook_pbp tradition: it re-derives everything it
//! needs from the raw CNF — strict XOR recovery (only complete canonical
//! 2^(k-1)-clause encodings, so every `rup` leaf in the emitted proof is
//! subsumed by, or propagation-refuted from, clauses that actually exist),
//! then GF(2) elimination with provenance to find an inconsistent subset S
//! (every variable appears an even number of times across S, parities sum
//! odd), then the GN21 construction per XOR in S:
//!
//!   - a chain of 1-bit full adders introduced by reification (`red`),
//!     whose pol-derived equalities give  Σx = 2·Σcarries + y'
//!   - y' = b by brute force: 2^k `rup` leaves + a `pol` resolution tree
//!   - folds producing   GEQ:  Σx − 2·Σcarries ≥ b
//!                       LEQ: −Σx + 2·Σcarries ≥ −b
//!
//! and the closing step: the pol-sum of the GEQs has all-even variable
//! coefficients but an odd RHS, so divide-by-2 rounds up; multiply by 2 and
//! add the summed LEQs → 0 ≥ 1.  Polynomial in the clausal encoding size.
//!
//! Port of `tools/cook_parity_proof.py` (validated against VeriPB 3.0.2 on
//! x2_64/x2_72, tseitingrid6x185, tseitin_n188_d3, tseitin_grid_n250
//! (62.5k XORs), tseitin_d3_n100000 (100k XORs)).

use std::collections::HashMap;
use std::io::{self, Write};

// ─── Wide bitset (the Python big-int masks) ─────────────────────────────────

#[derive(Clone, Default)]
struct Bits(Vec<u64>);

impl Bits {
    fn set(&mut self, i: usize) {
        let w = i / 64;
        if self.0.len() <= w {
            self.0.resize(w + 1, 0);
        }
        self.0[w] |= 1u64 << (i % 64);
    }

    fn xor_assign(&mut self, other: &Bits) {
        if self.0.len() < other.0.len() {
            self.0.resize(other.0.len(), 0);
        }
        for (i, &w) in other.0.iter().enumerate() {
            self.0[i] ^= w;
        }
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
    }

    fn top_bit(&self) -> Option<usize> {
        let last = self.0.last()?;
        Some((self.0.len() - 1) * 64 + (63 - last.leading_zeros() as usize))
    }

    fn ones(&self) -> Vec<usize> {
        let mut out = Vec::new();
        for (wi, &w) in self.0.iter().enumerate() {
            let mut w = w;
            while w != 0 {
                let b = w.trailing_zeros() as usize;
                out.push(wi * 64 + b);
                w &= w - 1;
            }
        }
        out
    }
}

// ─── Detection ──────────────────────────────────────────────────────────────

/// One recovered XOR constraint: `vars` (sorted, distinct) with parity `b`.
#[derive(Debug, Clone)]
pub struct Xor {
    pub vars: Vec<i32>,
    pub b: u8,
}

/// A parity refutation: the recovered XORs and the indices of an
/// inconsistent subset (sums to 0 = 1 over GF(2)).
#[derive(Debug)]
pub struct ParityRefutation {
    pub xors: Vec<Xor>,
    pub subset: Vec<usize>,
}

/// Strict XOR recovery: groups of clauses over the same variable set,
/// partitioned by EXCLUDED parity (so x^y=0 and x^y=1 over the same vars
/// both recover); a partition is an XOR iff it contains all 2^(k-1)
/// distinct wrong-parity assignments.
fn recover_xors(clauses: &[Vec<i32>]) -> Vec<Xor> {
    let mut groups: HashMap<Vec<i32>, Vec<usize>> = HashMap::new();
    for (i, c) in clauses.iter().enumerate() {
        if c.len() < 2 || c.len() > 24 {
            continue; // arity cap: 2^(k-1) clauses can't exist for huge k
        }
        let mut vs: Vec<i32> = c.iter().map(|l| l.abs()).collect();
        vs.sort_unstable();
        if vs.windows(2).any(|w| w[0] == w[1]) {
            continue; // duplicate var (tautology-ish) — not an XOR clause
        }
        groups.entry(vs).or_default().push(i);
    }
    let mut xors = Vec::new();
    for (vs, ids) in groups {
        let k = vs.len();
        let need = 1usize << (k - 1);
        if ids.len() < need {
            continue;
        }
        // Excluded assignment of a clause = each literal false; encode as a
        // bitmask over the sorted var positions; parity = #negative lits.
        let mut excl: [std::collections::HashSet<u32>; 2] =
            [Default::default(), Default::default()];
        for &ci in &ids {
            let c = &clauses[ci];
            let mut m: u32 = 0;
            let mut neg = 0usize;
            for &l in c {
                let pos = vs.binary_search(&l.abs()).unwrap();
                if l < 0 {
                    m |= 1 << pos;
                    neg += 1;
                }
            }
            excl[neg & 1].insert(m);
        }
        for par in 0..2usize {
            if excl[par].len() == need {
                xors.push(Xor { vars: vs.clone(), b: 1 - par as u8 });
            }
        }
    }
    xors
}

/// GF(2) elimination with provenance.  Returns the indices of an
/// inconsistent subset, or `None` if the XOR system is consistent.
fn ge_unsat_subset(xors: &[Xor]) -> Option<Vec<usize>> {
    let mut pivots: HashMap<usize, (Bits, u8, Bits)> = HashMap::new();
    for (i, x) in xors.iter().enumerate() {
        let mut mask = Bits::default();
        for &v in &x.vars {
            mask.set(v as usize);
        }
        let mut b = x.b;
        let mut prov = Bits::default();
        prov.set(i);
        loop {
            match mask.top_bit() {
                None => {
                    // Row reduced to 0 = b: inconsistent iff b == 1.
                    if b == 1 {
                        return Some(prov.ones());
                    }
                    break;
                }
                Some(piv) => {
                    if let Some((pm, pb, pp)) = pivots.get(&piv) {
                        let (pm, pb, pp) = (pm.clone(), *pb, pp.clone());
                        mask.xor_assign(&pm);
                        b ^= pb;
                        prov.xor_assign(&pp);
                    } else {
                        pivots.insert(piv, (mask, b, prov));
                        break;
                    }
                }
            }
        }
    }
    None
}

/// Detect a parity refutation in the CNF, or `None`.
pub fn detect_parity_refutation(clauses: &[Vec<i32>]) -> Option<ParityRefutation> {
    let xors = recover_xors(clauses);
    if xors.is_empty() {
        return None;
    }
    let subset = ge_unsat_subset(&xors)?;
    Some(ParityRefutation { xors, subset })
}

// ─── Emission ───────────────────────────────────────────────────────────────

struct Emit<'a, W: Write> {
    w: &'a mut W,
    id: usize,
}

impl<'a, W: Write> Emit<'a, W> {
    fn line(&mut self, s: &str) -> io::Result<()> {
        writeln!(self.w, "{}", s)
    }

    fn rule(&mut self, s: &str) -> io::Result<usize> {
        writeln!(self.w, "{}", s)?;
        self.id += 1;
        Ok(self.id)
    }
}

fn lit(v: usize, neg: bool) -> String {
    if neg { format!("~x{}", v) } else { format!("x{}", v) }
}

/// Emit the GN21 machinery for one XOR.  Returns (geq_id, leq_id, next_var).
fn emit_xor<W: Write>(
    e: &mut Emit<W>,
    vs: &[i32],
    b: u8,
    mut next_var: usize,
) -> io::Result<(usize, usize, usize)> {
    let k = vs.len();
    // adder chain: running sum bit `chain`, carries ys, forced-zero pads ws
    let mut adders: Vec<(usize, usize, usize, usize, usize)> = Vec::new();
    let mut ws: Vec<usize> = Vec::new();
    let mut chain = vs[0] as usize;
    let rest: Vec<usize> = vs[1..].iter().map(|&v| v as usize).collect();
    let mut i = 0;
    while i < rest.len() {
        let a = rest[i];
        let bb = if i + 1 < rest.len() {
            i += 2;
            rest[i - 1]
        } else {
            i += 1;
            let w = next_var;
            ws.push(w);
            next_var += 1;
            w
        };
        let y = next_var;
        let z = next_var + 1;
        next_var += 2;
        adders.push((chain, a, bb, y, z));
        chain = z;
    }
    let yp = chain; // y' = final sum bit
    // forced-zero pads
    let mut w_ids: HashMap<usize, usize> = HashMap::new();
    for &wv in &ws {
        let id = e.rule(&format!("red +1 {} >= 1 : x{} -> 0 ;", lit(wv, true), wv))?;
        w_ids.insert(wv, id);
    }
    // reifications + adder equalities
    let mut geq_ids = Vec::new();
    let mut leq_ids = Vec::new();
    for &(a, bb, c, y, z) in &adders {
        let r_ypos = e.rule(&format!(
            "red +2 {} +1 {} +1 {} +1 {} >= 2 : x{} -> 1 ;",
            lit(y, false), lit(a, true), lit(bb, true), lit(c, true), y))?;
        let r_yneg = e.rule(&format!(
            "red +2 {} +1 {} +1 {} +1 {} >= 2 : x{} -> 0 ;",
            lit(y, true), lit(a, false), lit(bb, false), lit(c, false), y))?;
        let r_zpos = e.rule(&format!(
            "red +3 {} +1 {} +1 {} +1 {} +2 {} >= 3 : x{} -> 1 ;",
            lit(z, false), lit(a, true), lit(bb, true), lit(c, true), lit(y, false), z))?;
        let r_zneg = e.rule(&format!(
            "red +3 {} +1 {} +1 {} +1 {} +2 {} >= 3 : x{} -> 0 ;",
            lit(z, true), lit(a, false), lit(bb, false), lit(c, false), lit(y, true), z))?;
        geq_ids.push(e.rule(&format!("pol {} {} 2 * + 3 d ;", r_zpos, r_ypos))?);
        leq_ids.push(e.rule(&format!("pol {} {} 2 * + 3 d ;", r_zneg, r_yneg))?);
    }
    // step 2: y'(b) >= 1 — 2^k rup leaves + resolution tree
    let ypb = lit(yp, b == 0);
    let mut cur: HashMap<u32, usize> = HashMap::new();
    for m in 0..(1u32 << k) {
        let mut terms = format!("+1 {}", ypb);
        for (j, &v) in vs.iter().enumerate() {
            let on = (m >> j) & 1 == 1;
            terms.push_str(&format!(" +1 {}", lit(v as usize, on)));
        }
        let id = e.rule(&format!("rup {} >= 1 ;", terms))?;
        cur.insert(m, id);
    }
    for j in (0..k).rev() {
        let mut nxt: HashMap<u32, usize> = HashMap::new();
        let keys: Vec<u32> = cur.keys().copied().collect();
        let mut sorted = keys;
        sorted.sort_unstable();
        for m in sorted {
            if (m >> j) & 1 == 1 {
                continue;
            }
            let a = cur[&m];
            let bb = cur[&(m | (1 << j))];
            let id = e.rule(&format!("pol {} {} + 2 d ;", a, bb))?;
            nxt.insert(m, id);
        }
        cur = nxt;
    }
    let ypb_id = cur[&0];
    // folds → GEQ / LEQ for the whole XOR
    let mut expr = leq_ids[0].to_string();
    for q in &leq_ids[1..] {
        expr.push_str(&format!(" {} +", q));
    }
    if b == 1 {
        expr.push_str(&format!(" {} +", ypb_id));
    } else {
        expr.push_str(&format!(" {} +", lit(yp, false)));
    }
    for &wv in &ws {
        expr.push_str(&format!(" {} +", w_ids[&wv]));
    }
    let geq = e.rule(&format!("pol {} ;", expr))?;
    let mut expr = geq_ids[0].to_string();
    for q in &geq_ids[1..] {
        expr.push_str(&format!(" {} +", q));
    }
    if b == 1 {
        expr.push_str(&format!(" {} +", lit(yp, true)));
    } else {
        expr.push_str(&format!(" {} +", ypb_id));
    }
    for &wv in &ws {
        expr.push_str(&format!(" {} +", lit(wv, false)));
    }
    let leq = e.rule(&format!("pol {} ;", expr))?;
    Ok((geq, leq, next_var))
}

/// Emit the full VeriPB proof for a parity refutation.
pub fn emit_parity_proof<W: Write>(
    pr: &ParityRefutation,
    n_clauses: usize,
    nvars: usize,
    w: &mut W,
) -> io::Result<()> {
    let mut e = Emit { w, id: n_clauses };
    e.line("pseudo-Boolean proof version 3.0")?;
    e.line(&format!(
        "% certified parity refutation (GN21): {} XOR(s) in the inconsistent subset",
        pr.subset.len()))?;
    e.line(&format!("f {};", n_clauses))?;
    let mut next_var = nvars + 1;
    let mut geqs = Vec::with_capacity(pr.subset.len());
    let mut leqs = Vec::with_capacity(pr.subset.len());
    for &i in &pr.subset {
        let x = &pr.xors[i];
        let (g, l, nv) = emit_xor(&mut e, &x.vars, x.b, next_var)?;
        geqs.push(g);
        leqs.push(l);
        next_var = nv;
    }
    // batched sums (avoid one giant pol line)
    fn batch_sum<W: Write>(e: &mut Emit<W>, ids: &[usize]) -> io::Result<usize> {
        let mut cur: Vec<usize> = ids.to_vec();
        while cur.len() > 1 {
            let mut nxt = Vec::new();
            for chunk in cur.chunks(512) {
                if chunk.len() == 1 {
                    nxt.push(chunk[0]);
                    continue;
                }
                let mut expr = chunk[0].to_string();
                for q in &chunk[1..] {
                    expr.push_str(&format!(" {} +", q));
                }
                nxt.push(e.rule(&format!("pol {} ;", expr))?);
            }
            cur = nxt;
        }
        Ok(cur[0])
    }
    let gsum = batch_sum(&mut e, &geqs)?;
    let lsum = batch_sum(&mut e, &leqs)?;
    e.rule(&format!("pol {} 2 d 2 * {} + ;", gsum, lsum))?;
    e.line("rup >= 1 ;")?;
    e.id += 1;
    e.line("")?;
    e.line("output NONE;")?;
    e.line("conclusion UNSAT : -1;")?;
    e.line("end pseudo-Boolean proof;")?;
    Ok(())
}

// ─── Tests ──────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detect_minimal_contradiction() {
        // x1^x2=1 and x1^x2=0 over the same var set.
        let cnf: Vec<Vec<i32>> = vec![
            vec![1, 2], vec![-1, -2],   // = 1
            vec![-1, 2], vec![1, -2],   // = 0
        ];
        let pr = detect_parity_refutation(&cnf).expect("refutation");
        assert_eq!(pr.xors.len(), 2);
        assert_eq!(pr.subset.len(), 2);
        let mut buf = Vec::new();
        emit_parity_proof(&pr, cnf.len(), 2, &mut buf).unwrap();
        let s = String::from_utf8(buf).unwrap();
        assert!(s.starts_with("pseudo-Boolean proof version 3.0"));
        assert!(s.contains("red +1 ~x3 >= 1 : x3 -> 0 ;")); // pad for arity-2
        assert!(s.ends_with("end pseudo-Boolean proof;\n"));
    }

    #[test]
    fn consistent_system_is_none() {
        // x1^x2=1, x2^x3=1 — consistent.
        let cnf: Vec<Vec<i32>> = vec![
            vec![1, 2], vec![-1, -2],
            vec![2, 3], vec![-2, -3],
        ];
        assert!(detect_parity_refutation(&cnf).is_none());
    }

    #[test]
    fn arity3_chain_contradiction() {
        // x1^x2^x3=0 (4 clauses) + x1^x2=1 + x3=... use x1^x2^x3=0 and
        // x1^x2^x3=1: direct contradiction at arity 3.
        let cnf: Vec<Vec<i32>> = vec![
            // = 0: exclude odd assignments
            vec![-1, 2, 3], vec![1, -2, 3], vec![1, 2, -3], vec![-1, -2, -3],
            // = 1: exclude even assignments
            vec![1, 2, 3], vec![-1, -2, 3], vec![-1, 2, -3], vec![1, -2, -3],
        ];
        let pr = detect_parity_refutation(&cnf).expect("refutation");
        assert_eq!(pr.subset.len(), 2);
        let mut buf = Vec::new();
        emit_parity_proof(&pr, cnf.len(), 3, &mut buf).unwrap();
        assert!(String::from_utf8(buf).unwrap().contains("conclusion UNSAT"));
    }
}
