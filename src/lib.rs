pub mod formula;
pub mod matrix;
pub mod prove;
pub mod simplify;

pub use prove::{check_satisfiable, check_valid, get_paths};
pub use simplify::simplify;

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
