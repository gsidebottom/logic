use std::collections::{BTreeSet, HashMap, HashSet};
use crate::formula::Node;

// term values: 0=false, 1=true, 2=don't-care
#[derive(Clone)]
pub struct Implicant {
    pub term: Vec<u8>,
    pub covered: BTreeSet<usize>,
}

pub fn combine(a: &[u8], b: &[u8]) -> Option<Vec<u8>> {
    let mut diffs = 0;
    let mut diff_pos = 0;
    for i in 0..a.len() {
        if a[i] != b[i] {
            if a[i] == 2 || b[i] == 2 { return None; }
            diffs += 1;
            if diffs > 1 { return None; }
            diff_pos = i;
        }
    }
    if diffs == 1 {
        let mut result = a.to_vec();
        result[diff_pos] = 2;
        Some(result)
    } else {
        None
    }
}

pub fn qmc(minterms: &[usize], n: usize) -> Vec<Implicant> {
    let mut current: Vec<Implicant> = {
        let mut seen = HashSet::new();
        minterms.iter().filter_map(|&m| {
            let term: Vec<u8> = (0..n).map(|j| ((m >> (n - 1 - j)) & 1) as u8).collect();
            if seen.insert(term.clone()) {
                Some(Implicant { term, covered: BTreeSet::from([m]) })
            } else {
                None
            }
        }).collect()
    };

    let mut primes = Vec::new();

    while !current.is_empty() {
        let mut used = HashSet::new();
        let mut next_map: HashMap<Vec<u8>, Implicant> = HashMap::new();

        for i in 0..current.len() {
            for j in (i + 1)..current.len() {
                if let Some(c) = combine(&current[i].term, &current[j].term) {
                    used.insert(i);
                    used.insert(j);
                    let entry = next_map.entry(c.clone()).or_insert(Implicant {
                        term: c,
                        covered: BTreeSet::new(),
                    });
                    entry.covered.extend(&current[i].covered);
                    entry.covered.extend(&current[j].covered);
                }
            }
        }

        for (i, imp) in current.iter().enumerate() {
            if !used.contains(&i) {
                primes.push(imp.clone());
            }
        }
        current = next_map.into_values().collect();
    }

    primes
}

pub fn simplify(formula: &str) -> Result<String, String> {
    simplify_dnf(formula)
}

pub fn simplify_dnf(formula: &str) -> Result<String, String> {
    let ast = Node::try_from(formula)?;
    let vars: Vec<String> = ast.extract_vars().into_iter().collect();
    let n = vars.len();

    if n == 0 { return Ok(ast.evaluate(&HashMap::new()).to_string()); }

    let mut minterms = Vec::new();
    for i in 0..(1usize << n) {
        let mut asgn = HashMap::new();
        for (j, v) in vars.iter().enumerate() {
            asgn.insert(v.clone(), ((i >> (n - 1 - j)) & 1) as u8);
        }
        if ast.evaluate(&asgn) == 1 {
            minterms.push(i);
        }
    }

    if minterms.is_empty() { return Ok("0".to_string()); }
    if minterms.len() == 1 << n { return Ok("1".to_string()); }

    let primes = qmc(&minterms, n);
    let cover = minimal_cover(&primes, &minterms);

    let result = cover.iter().map(|imp| {
        let lits: Vec<String> = vars.iter().enumerate().filter_map(|(i, v)| {
            match imp.term[i] {
                1 => Some(v.clone()),
                0 => Some(format!("{}'", v)),
                _ => None,
            }
        }).collect();
        if lits.is_empty() { "1".to_string() } else { lits.join("·") }
    }).collect::<Vec<_>>().join(" + ");

    Ok(result)
}

pub fn simplify_cnf(formula: &str) -> Result<String, String> {
    let ast = Node::try_from(formula)?;
    let vars: Vec<String> = ast.extract_vars().into_iter().collect();
    let n = vars.len();

    if n == 0 { return Ok(ast.evaluate(&HashMap::new()).to_string()); }

    // Maxterms: rows where the formula evaluates to FALSE.
    let mut maxterms = Vec::new();
    for i in 0..(1usize << n) {
        let mut asgn = HashMap::new();
        for (j, v) in vars.iter().enumerate() {
            asgn.insert(v.clone(), ((i >> (n - 1 - j)) & 1) as u8);
        }
        if ast.evaluate(&asgn) == 0 {
            maxterms.push(i);
        }
    }

    if maxterms.is_empty() { return Ok("1".to_string()); }
    if maxterms.len() == 1 << n { return Ok("0".to_string()); }

    // Run QMC on the FALSE rows to find minimal cover of maxterms.
    let primes = qmc(&maxterms, n);
    let cover = minimal_cover(&primes, &maxterms);

    // Each implicant of the FALSE rows represents a clause via De Morgan:
    // a row with assignment (v=0 → v, v=1 → v') becomes a sum (OR clause).
    let result = cover.iter().map(|imp| {
        let lits: Vec<String> = vars.iter().enumerate().filter_map(|(i, v)| {
            match imp.term[i] {
                0 => Some(v.clone()),         // false in maxterm → positive in clause
                1 => Some(format!("{}'", v)), // true  in maxterm → negative in clause
                _ => None,
            }
        }).collect();
        if lits.is_empty() { "0".to_string() } else { format!("({})", lits.join(" + ")) }
    }).collect::<Vec<_>>().join("·");

    Ok(result)
}

pub fn minimal_cover(primes: &[Implicant], minterms: &[usize]) -> Vec<Implicant> {
    let mut result: Vec<Implicant> = Vec::new();
    let mut covered: BTreeSet<usize> = BTreeSet::new();

    // Essential prime implicants
    for &m in minterms {
        let covering: Vec<_> = primes.iter().filter(|p| p.covered.contains(&m)).collect();
        if covering.len() == 1 && !result.iter().any(|r| r.term == covering[0].term) {
            covered.extend(&covering[0].covered);
            result.push(covering[0].clone());
        }
    }

    // Greedy cover of remaining minterms
    let mut uncovered: BTreeSet<usize> = minterms.iter()
        .filter(|m| !covered.contains(m))
        .cloned()
        .collect();

    while !uncovered.is_empty() {
        let best = primes.iter()
            .filter(|p| !result.iter().any(|r| r.term == p.term))
            .max_by_key(|p| p.covered.iter().filter(|m| uncovered.contains(m)).count());

        match best {
            Some(b) => {
                let b = b.clone();
                b.covered.iter().for_each(|m| { uncovered.remove(m); });
                result.push(b);
            }
            None => break,
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(formula: &str) -> String {
        simplify(formula).unwrap_or_else(|e| panic!("Expected simplify to succeed for {:?}: {}", formula, e))
    }

    fn s_err(formula: &str) -> String {
        simplify(formula).unwrap_err()
    }

    fn sort_sop(result: &str) -> String {
        let mut terms: Vec<&str> = result.split(" + ").collect();
        terms.sort();
        terms.join(" + ")
    }

    fn s_sorted(formula: &str) -> String {
        sort_sop(&s(formula))
    }

    // ── Constants ────────────────────────────────────────────────────────────────

    #[test]
    fn test_constant_0() { assert_eq!(s("0"), "0"); }

    #[test]
    fn test_constant_1() { assert_eq!(s("1"), "1"); }

    #[test]
    fn test_constant_0_prime() { assert_eq!(s("0'"), "1"); }

    #[test]
    fn test_constant_1_prime() { assert_eq!(s("1'"), "0"); }

    #[test]
    fn test_constant_double_prime() {
        assert_eq!(s("0''"), "0");
        assert_eq!(s("1''"), "1");
    }

    #[test]
    fn test_constant_expressions() {
        assert_eq!(s("0 + 0"), "0");
        assert_eq!(s("1 + 1"), "1");
        assert_eq!(s("0 · 0"), "0");
        assert_eq!(s("1 · 1"), "1");
        assert_eq!(s("0 + 1"), "1");
        assert_eq!(s("0 · 1"), "0");
        assert_eq!(s("1'· 0'"), "0");
    }

    // ── Identity laws ────────────────────────────────────────────────────────────

    #[test]
    fn test_identity_or_0() {
        assert_eq!(s("A + 0"), "A");
        assert_eq!(s("0 + A"), "A");
    }

    #[test]
    fn test_identity_and_1() {
        assert_eq!(s("A · 1"), "A");
        assert_eq!(s("1 · A"), "A");
    }

    // ── Annihilation laws ────────────────────────────────────────────────────────

    #[test]
    fn test_annihilation_or_1() {
        assert_eq!(s("A + 1"), "1");
        assert_eq!(s("1 + A"), "1");
    }

    #[test]
    fn test_annihilation_and_0() {
        assert_eq!(s("A · 0"), "0");
        assert_eq!(s("0 · A"), "0");
    }

    // ── Idempotent & complement laws ─────────────────────────────────────────────

    #[test]
    fn test_idempotent() {
        assert_eq!(s("A + A"), "A");
        assert_eq!(s("A · A"), "A");
    }

    #[test]
    fn test_complement() {
        assert_eq!(s("A + A'"), "1");
        assert_eq!(s("A · A'"), "0");
    }

    #[test]
    fn test_double_complement() {
        assert_eq!(s("A''"), "A");
        assert_eq!(s("A'''"), "A'");
    }

    // ── Absorption ───────────────────────────────────────────────────────────────

    #[test]
    fn test_absorption_or() {
        assert_eq!(s("A + A·B"), "A");
        assert_eq!(s("A + A·B·C"), "A");
    }

    #[test]
    fn test_absorption_and() {
        assert_eq!(s("A · (A + B)"), "A");
    }

    // ── De Morgan ────────────────────────────────────────────────────────────────

    #[test]
    fn test_de_morgan_equivalent() {
        assert_eq!(s_sorted("A'·B' + A'·B + A·B'"),
                   s_sorted("A' + B'"));
    }

    // ── Consensus theorem ────────────────────────────────────────────────────────

    #[test]
    fn test_consensus() {
        assert_eq!(s_sorted("A·B + A'·C + B·C"),
                   s_sorted("A·B + A'·C"));
    }

    // ── Distributive ─────────────────────────────────────────────────────────────

    #[test]
    fn test_distributive() {
        assert_eq!(s_sorted("A·(B + C)"),
                   s_sorted("A·B + A·C"));
    }

    // ── Three-variable reduction ─────────────────────────────────────────────────

    #[test]
    fn test_three_var_merge() {
        assert_eq!(s("A·B·C + A·B·C'"), "A·B");
    }

    #[test]
    fn test_three_var_absorption_variant() {
        assert_eq!(s_sorted("A + A'·B"), s_sorted("A + B"));
    }

    // ── XOR (irreducible in SOP) ─────────────────────────────────────────────────

    #[test]
    fn test_xor_stays_two_terms() {
        let result = s("A·B' + A'·B");
        assert!(result.contains(" + "), "XOR should remain two terms, got: {}", result);
    }

    #[test]
    fn test_xor_equivalent_forms() {
        assert_eq!(s_sorted("A·B' + A'·B"),
                   s_sorted("(A + B)·(A' + B')"));
    }

    // ── Implicit AND ─────────────────────────────────────────────────────────────

    #[test]
    fn test_implicit_and_space() {
        assert_eq!(s("A B + A B'"), "A");
    }

    #[test]
    fn test_implicit_and_groups() {
        assert_eq!(s("(A+B)(A+B')"), "A");
    }

    // ── App example ──────────────────────────────────────────────────────────────

    #[test]
    fn test_app_example() {
        assert_eq!(s("((A·B) + (A'+B')) · ((A'+B') + (A·B))"), "1");
    }

    // ── Multichar variable names ─────────────────────────────────────────────────

    #[test]
    fn test_multichar_complement() {
        assert_eq!(s("foo + foo'"),         "1");
        assert_eq!(s("my_var · my_var'"),   "0");
        assert_eq!(s("foo · foo"),          "foo");
    }

    #[test]
    fn test_multichar_reduction() {
        assert_eq!(s("foo·bar + foo·bar'"), "foo");
    }

    // ── Error cases ──────────────────────────────────────────────────────────────

    #[test]
    fn test_propagates_parse_errors() {
        assert!(s_err("'A").contains("complement"));
        assert!(s_err("2 + B").contains("digit"));
        assert!(s_err("A +").contains("Expected"));
    }
}
