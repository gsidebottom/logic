use std::collections::{BTreeSet, HashMap, HashSet};

pub mod formula;
pub mod matrix;

use formula::{count_primes, evaluate, extract_vars, get_base_name, parse, Node};

// ─── Quine-McCluskey ──────────────────────────────────────────────────────────

// term values: 0=false, 1=true, 2=don't-care
#[derive(Clone)]
struct Implicant {
    term: Vec<u8>,
    covered: BTreeSet<usize>,
}

fn combine(a: &[u8], b: &[u8]) -> Option<Vec<u8>> {
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

fn qmc(minterms: &[usize], n: usize) -> Vec<Implicant> {
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

fn minimal_cover(primes: &[Implicant], minterms: &[usize]) -> Vec<Implicant> {
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

// ─── Matrix conversion ────────────────────────────────────────────────────────

fn node_to_matrix(node: &Node, var_index: &HashMap<String, u32>) -> matrix::Matrix {
    match node {
        Node::Var(name) => {
            let base = get_base_name(name);
            let neg  = count_primes(name) % 2 == 1;
            match base {
                "0" => if neg { matrix::Matrix::Prod(vec![]) } else { matrix::Matrix::Sum(vec![]) },
                "1" => if neg { matrix::Matrix::Sum(vec![]) } else { matrix::Matrix::Prod(vec![]) },
                _   => matrix::Matrix::Lit(matrix::Lit { var: *var_index.get(base).unwrap(), neg }),
            }
        }
        Node::And(ch) => matrix::Matrix::Prod(ch.iter().map(|c| node_to_matrix(c, var_index)).collect()),
        Node::Or(ch)  => matrix::Matrix::Sum(ch.iter().map(|c| node_to_matrix(c, var_index)).collect()),
    }
}

fn format_path(path: &matrix::Path, var_names: &[String]) -> String {
    if path.is_empty() { return "∅".to_string(); }
    let mut lits: Vec<String> = path.iter().map(|l| {
        let name = &var_names[l.var as usize];
        if l.neg { format!("{}'", name) } else { name.clone() }
    }).collect();
    lits.sort();
    format!("{{{}}}", lits.join(", "))
}

fn parse_to_matrix(formula: &str) -> Result<(matrix::Matrix, Vec<String>), String> {
    let ast  = parse(formula)?;
    let vars: Vec<String> = extract_vars(&ast).into_iter().collect();
    if vars.len() > 20 {
        return Err("Too many variables for matrix analysis (max 20)".to_string());
    }
    let idx: HashMap<String, u32> = vars.iter().enumerate().map(|(i, v)| (v.clone(), i as u32)).collect();
    Ok((node_to_matrix(&ast, &idx), vars))
}

// ─── Public API ───────────────────────────────────────────────────────────────

pub fn get_paths(formula: &str) -> Result<(Vec<String>, Vec<bool>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    let formatted  = all_paths.iter().map(|p| format_path(p, &vars)).collect();
    let comp_flags = all_paths.iter().map(|p| matrix::is_complementary(p)).collect();
    Ok((formatted, comp_flags))
}

pub fn simplify(formula: &str) -> Result<String, String> {
    let ast = parse(formula)?;
    let vars: Vec<String> = extract_vars(&ast).into_iter().collect();
    let n = vars.len();

    if n == 0 { return Ok(evaluate(&ast, &HashMap::new()).to_string()); }
    if n > 10 { return Err("Too many variables to simplify (max 10)".to_string()); }

    let mut minterms = Vec::new();
    for i in 0..(1usize << n) {
        let mut asgn = HashMap::new();
        for (j, v) in vars.iter().enumerate() {
            asgn.insert(v.clone(), ((i >> (n - 1 - j)) & 1) as u8);
        }
        if evaluate(&ast, &asgn) == 1 {
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

/// Greedy set cover: find a small set of variables whose complementary pairs
/// collectively appear in every path. Returns variable indices in cover order.
fn greedy_cover(paths: &[matrix::Path], n_vars: usize) -> Vec<usize> {
    let covers: Vec<Vec<usize>> = (0..n_vars as u32).map(|var| {
        let pos = matrix::Lit { var, neg: false };
        let neg = matrix::Lit { var, neg: true  };
        paths.iter().enumerate()
            .filter(|(_, p)| p.contains(&pos) && p.contains(&neg))
            .map(|(i, _)| i)
            .collect()
    }).collect();

    let mut uncovered: BTreeSet<usize> = (0..paths.len()).collect();
    let mut used      = vec![false; n_vars];
    let mut result    = Vec::new();

    while !uncovered.is_empty() {
        let best = (0..n_vars)
            .filter(|&v| !used[v])
            .max_by_key(|&v| covers[v].iter().filter(|i| uncovered.contains(i)).count());
        match best {
            Some(v) => {
                covers[v].iter().for_each(|i| { uncovered.remove(i); });
                used[v] = true;
                result.push(v);
            }
            None => break,
        }
    }
    result
}

/// Returns `(true, None, pairs)` if valid (with a greedy cover of complementary
/// pairs), or `(false, Some(path), [])` with the first uncomplimentary path.
pub fn check_valid(formula: &str) -> Result<(bool, Option<String>, Vec<String>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let all_paths = matrix::paths(&m);
    match all_paths.iter().find(|p| !matrix::is_complementary(p)) {
        Some(path) => Ok((false, Some(format_path(path, &vars)), vec![])),
        None => {
            let cover = greedy_cover(&all_paths, vars.len());
            let pairs = cover.iter()
                .map(|&v| format!("{{{}, {}'}}", vars[v], vars[v]))
                .collect();
            Ok((true, None, pairs))
        }
    }
}

/// Returns `(true, Some(path), [])` with first uncomplimentary path in the
/// complement if satisfiable, or `(false, None, pairs)` with a greedy cover of
/// complementary pairs in the complement if unsatisfiable.
pub fn check_satisfiable(formula: &str) -> Result<(bool, Option<String>, Vec<String>), String> {
    let (m, vars) = parse_to_matrix(formula)?;
    let comp_paths = matrix::paths(&m.complement());
    match comp_paths.iter().find(|p| !matrix::is_complementary(p)) {
        Some(path) => Ok((true, Some(format_path(path, &vars)), vec![])),
        None => {
            let cover = greedy_cover(&comp_paths, vars.len());
            let pairs = cover.iter()
                .map(|&v| format!("{{{}, {}'}}", vars[v], vars[v]))
                .collect();
            Ok((false, None, pairs))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use formula::{parse, Node};

    // ── Helpers ───────────────────────────────────────────────────────────────────

    fn parse_ok(s: &str) -> Node {
        parse(s).unwrap_or_else(|e| panic!("Expected parse to succeed for {:?}: {}", s, e))
    }

    fn s(formula: &str) -> String {
        simplify(formula).unwrap_or_else(|e| panic!("Expected simplify to succeed for {:?}: {}", formula, e))
    }

    fn s_err(formula: &str) -> String {
        simplify(formula).unwrap_err()
    }

    /// Sort terms in a sum-of-products string for order-independent comparison.
    fn sort_sop(result: &str) -> String {
        let mut terms: Vec<&str> = result.split(" + ").collect();
        terms.sort();
        terms.join(" + ")
    }

    fn s_sorted(formula: &str) -> String {
        sort_sop(&s(formula))
    }

    // ── Tokenizer / Parser ────────────────────────────────────────────────────────

    #[test]
    fn test_parse_empty() {
        assert!(parse("").is_err());
        assert!(parse("   ").is_err());
    }

    #[test]
    fn test_parse_single_var() {
        assert!(matches!(parse_ok("A"),       Node::Var(n) if n == "A"));
        assert!(matches!(parse_ok("foo_bar"), Node::Var(n) if n == "foo_bar"));
        assert!(matches!(parse_ok("x123"),    Node::Var(n) if n == "x123"));
    }

    #[test]
    fn test_parse_primes() {
        assert!(matches!(parse_ok("A'"),  Node::Var(n) if n == "A'"));
        assert!(matches!(parse_ok("A''"), Node::Var(n) if n == "A''"));
        assert!(matches!(parse_ok("A '"), Node::Var(n) if n == "A'"));   // space before prime
        assert!(matches!(parse_ok("foo_bar'"), Node::Var(n) if n == "foo_bar'"));
    }

    #[test]
    fn test_parse_literals() {
        assert!(matches!(parse_ok("0"),  Node::Var(n) if n == "0"));
        assert!(matches!(parse_ok("1"),  Node::Var(n) if n == "1"));
        assert!(matches!(parse_ok("0'"), Node::Var(n) if n == "0'"));
        assert!(matches!(parse_ok("1'"), Node::Var(n) if n == "1'"));
        assert!(matches!(parse_ok("0 '"), Node::Var(n) if n == "0'"));  // space before prime
    }

    #[test]
    fn test_parse_and_operators() {
        assert!(matches!(parse_ok("A · B"), Node::And(_)));
        assert!(matches!(parse_ok("A * B"), Node::And(_)));
        assert!(matches!(parse_ok("A . B"), Node::And(_)));
    }

    #[test]
    fn test_parse_or() {
        assert!(matches!(parse_ok("A + B"), Node::Or(_)));
    }

    #[test]
    fn test_parse_implicit_and_vars() {
        assert!(matches!(parse_ok("A B"), Node::And(_)));
    }

    #[test]
    fn test_parse_implicit_and_groups() {
        assert!(matches!(parse_ok("(A+B)(C+D)"), Node::And(_)));
        assert!(matches!(parse_ok("B(C+D)"),     Node::And(_)));
    }

    #[test]
    fn test_parse_precedence_and_over_or() {
        // A + B·C should parse as A + (B·C), i.e. outer node is OR
        let node = parse_ok("A + B · C");
        assert!(matches!(node, Node::Or(_)));
        if let Node::Or(children) = node {
            assert!(matches!(children[1], Node::And(_)));
        }
    }

    #[test]
    fn test_parse_multichar_vars() {
        assert!(matches!(parse_ok("foo · bar"), Node::And(_)));
        assert!(matches!(parse_ok("my_var' + other_var"), Node::Or(_)));
    }

    #[test]
    fn test_parse_nested_parens() {
        assert!(parse_ok("((A + B))").is_var_or_op());
        assert!(parse("(A + B").is_err());
        assert!(parse("A + B)").is_err());
    }

    #[test]
    fn test_parse_error_stray_prime() {
        assert!(parse("'A").is_err());
        assert!(parse("A + 'B").is_err());
        assert!(parse("(A * 'B)").is_err());
    }

    #[test]
    fn test_parse_error_digit_start() {
        assert!(parse("2A").is_err());
        assert!(parse("9").is_err());
        assert!(parse("1B").is_ok());   // 1 is a literal; B is a separate var — parses as 1·B
    }

    #[test]
    fn test_parse_error_missing_operand() {
        assert!(parse("A +").is_err());
        assert!(parse("+ A").is_err());
        assert!(parse("A · · B").is_err());
        assert!(parse("()").is_err());
    }

    // ── Simplification: constants ─────────────────────────────────────────────────

    #[test]
    fn test_simplify_constant_0() { assert_eq!(s("0"), "0"); }

    #[test]
    fn test_simplify_constant_1() { assert_eq!(s("1"), "1"); }

    #[test]
    fn test_simplify_constant_0_prime() { assert_eq!(s("0'"), "1"); }

    #[test]
    fn test_simplify_constant_1_prime() { assert_eq!(s("1'"), "0"); }

    #[test]
    fn test_simplify_constant_double_prime() {
        assert_eq!(s("0''"), "0");
        assert_eq!(s("1''"), "1");
    }

    #[test]
    fn test_simplify_constant_expressions() {
        assert_eq!(s("0 + 0"), "0");
        assert_eq!(s("1 + 1"), "1");
        assert_eq!(s("0 · 0"), "0");
        assert_eq!(s("1 · 1"), "1");
        assert_eq!(s("0 + 1"), "1");
        assert_eq!(s("0 · 1"), "0");
        assert_eq!(s("1'· 0'"), "0");  // 0 · 1 = 0
    }

    // ── Simplification: identity laws ────────────────────────────────────────────

    #[test]
    fn test_simplify_identity_or_0() {
        assert_eq!(s("A + 0"), "A");
        assert_eq!(s("0 + A"), "A");
    }

    #[test]
    fn test_simplify_identity_and_1() {
        assert_eq!(s("A · 1"), "A");
        assert_eq!(s("1 · A"), "A");
    }

    // ── Simplification: annihilation laws ────────────────────────────────────────

    #[test]
    fn test_simplify_annihilation_or_1() {
        assert_eq!(s("A + 1"), "1");
        assert_eq!(s("1 + A"), "1");
    }

    #[test]
    fn test_simplify_annihilation_and_0() {
        assert_eq!(s("A · 0"), "0");
        assert_eq!(s("0 · A"), "0");
    }

    // ── Simplification: idempotent & complement laws ──────────────────────────────

    #[test]
    fn test_simplify_idempotent() {
        assert_eq!(s("A + A"), "A");
        assert_eq!(s("A · A"), "A");
    }

    #[test]
    fn test_simplify_complement() {
        assert_eq!(s("A + A'"), "1");
        assert_eq!(s("A · A'"), "0");
    }

    #[test]
    fn test_simplify_double_complement() {
        assert_eq!(s("A''"), "A");
        assert_eq!(s("A'''"), "A'");
    }

    // ── Simplification: absorption ────────────────────────────────────────────────

    #[test]
    fn test_simplify_absorption_or() {
        assert_eq!(s("A + A·B"), "A");
        assert_eq!(s("A + A·B·C"), "A");
    }

    #[test]
    fn test_simplify_absorption_and() {
        assert_eq!(s("A · (A + B)"), "A");
    }

    // ── Simplification: De Morgan ─────────────────────────────────────────────────

    #[test]
    fn test_simplify_de_morgan_equivalent() {
        assert_eq!(s_sorted("A'·B' + A'·B + A·B'"),
                   s_sorted("A' + B'"));
    }

    // ── Simplification: consensus theorem ────────────────────────────────────────

    #[test]
    fn test_simplify_consensus() {
        assert_eq!(s_sorted("A·B + A'·C + B·C"),
                   s_sorted("A·B + A'·C"));
    }

    // ── Simplification: distributive ─────────────────────────────────────────────

    #[test]
    fn test_simplify_distributive() {
        assert_eq!(s_sorted("A·(B + C)"),
                   s_sorted("A·B + A·C"));
    }

    // ── Simplification: three-variable reduction ──────────────────────────────────

    #[test]
    fn test_simplify_three_var_merge() {
        assert_eq!(s("A·B·C + A·B·C'"), "A·B");
    }

    #[test]
    fn test_simplify_three_var_absorption_variant() {
        assert_eq!(s_sorted("A + A'·B"), s_sorted("A + B"));
    }

    // ── Simplification: XOR (irreducible in SOP) ─────────────────────────────────

    #[test]
    fn test_simplify_xor_stays_two_terms() {
        let result = s("A·B' + A'·B");
        assert!(result.contains(" + "), "XOR should remain two terms, got: {}", result);
    }

    #[test]
    fn test_simplify_xor_equivalent_forms() {
        assert_eq!(s_sorted("A·B' + A'·B"),
                   s_sorted("(A + B)·(A' + B')"));
    }

    // ── Simplification: implicit AND ─────────────────────────────────────────────

    #[test]
    fn test_simplify_implicit_and_space() {
        assert_eq!(s("A B + A B'"), "A");
    }

    #[test]
    fn test_simplify_implicit_and_groups() {
        assert_eq!(s("(A+B)(A+B')"), "A");
    }

    // ── Simplification: app example ───────────────────────────────────────────────

    #[test]
    fn test_simplify_app_example() {
        assert_eq!(s("((A·B) + (A'+B')) · ((A'+B') + (A·B))"), "1");
    }

    // ── Simplification: multichar variable names ──────────────────────────────────

    #[test]
    fn test_simplify_multichar_complement() {
        assert_eq!(s("foo + foo'"),         "1");
        assert_eq!(s("my_var · my_var'"),   "0");
        assert_eq!(s("foo · foo"),          "foo");
    }

    #[test]
    fn test_simplify_multichar_reduction() {
        assert_eq!(s("foo·bar + foo·bar'"), "foo");
    }

    // ── Error cases ───────────────────────────────────────────────────────────────

    #[test]
    fn test_simplify_too_many_vars() {
        assert!(simplify("a+b+c+d+e+f+g+h+i+j+k").is_err());
    }

    #[test]
    fn test_simplify_propagates_parse_errors() {
        assert!(s_err("'A").contains("complement"));
        assert!(s_err("2 + B").contains("digit"));
        assert!(s_err("A +").contains("Expected"));
    }

    // ── Helper trait for test readability ────────────────────────────────────────

    trait NodeExt { fn is_var_or_op(&self) -> bool; }
    impl NodeExt for Node {
        fn is_var_or_op(&self) -> bool { true }
    }
}
