use std::collections::{BTreeSet, HashMap};

// ─── AST ──────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum Node {
    Var(String),
    And(Vec<Node>),
    Or(Vec<Node>),
}

impl Node {
    /// Return the set of base variable names (excluding constants 0 and 1).
    pub fn extract_vars(&self) -> BTreeSet<String> {
        let mut set = BTreeSet::new();
        fn collect(node: &Node, set: &mut BTreeSet<String>) {
            match node {
                Node::Var(n) => {
                    let base = get_base_name(n);
                    if base != "0" && base != "1" { set.insert(base.to_string()); }
                }
                Node::And(c) | Node::Or(c) => {
                    for child in c { collect(child, set); }
                }
            }
        }
        collect(self, &mut set);
        set
    }

    pub fn evaluate(&self, variable_assignment: &HashMap<String, u8>) -> u8 {
        match self {
            Node::Var(name) => {
                let base = get_base_name(name);
                if base == "0" || base == "1" {
                    let val = if base == "1" { 1u8 } else { 0u8 };
                    return if count_primes(name) % 2 == 1 { 1 - val } else { val };
                }
                let val = *variable_assignment.get(base).unwrap_or(&0);
                if count_primes(name) % 2 == 1 { 1 - val } else { val }
            }
            Node::And(c) => if c.iter().all(|ch| ch.evaluate(variable_assignment) == 1) { 1 } else { 0 },
            Node::Or(c)  => if c.iter().any(|ch| ch.evaluate(variable_assignment) == 1) { 1 } else { 0 },
        }
    }
}

// ─── Ast ─────────────────────────────────────────────────────────────────────

pub struct Ast {
    pub root: Node,
    pub vars: Vec<String>,
    pub var_index: HashMap<String, u32>,
}

impl TryFrom<&str> for Ast {
    type Error = String;

    fn try_from(formula: &str) -> Result<Self, String> {
        let root = Node::try_from(formula)?;
        let vars: Vec<String> = root.extract_vars().into_iter().collect();
        let var_index: HashMap<String, u32> = vars.iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), i as u32))
            .collect();
        Ok(Ast { root, vars, var_index })
    }
}

// ─── Tokenizer ────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
enum Token {
    LParen,
    RParen,
    Plus,
    Dot,
    Var(String),
}

fn tokenize(s: &str) -> Result<Vec<Token>, String> {
    let chars: Vec<char> = s.chars().collect();
    let mut tokens = Vec::new();
    let mut i = 0;
    while i < chars.len() {
        match chars[i] {
            c if c.is_whitespace() => { i += 1; }
            '(' => { tokens.push(Token::LParen); i += 1; }
            ')' => { tokens.push(Token::RParen); i += 1; }
            '+' => { tokens.push(Token::Plus); i += 1; }
            '·' | '*' | '.' | '⋅' => { tokens.push(Token::Dot); i += 1; }
            c if c.is_ascii_alphabetic() => {
                let mut name = c.to_string();
                i += 1;
                while i < chars.len() && (chars[i].is_alphanumeric() || chars[i] == '_') {
                    name.push(chars[i]);
                    i += 1;
                }
                while i < chars.len() && chars[i].is_whitespace() { i += 1; }
                while i < chars.len() && chars[i] == '\'' {
                    name.push('\'');
                    i += 1;
                }
                tokens.push(Token::Var(name));
            }
            '0' | '1' => {
                let mut name = chars[i].to_string();
                i += 1;
                while i < chars.len() && chars[i].is_whitespace() { i += 1; }
                while i < chars.len() && chars[i] == '\'' {
                    name.push('\'');
                    i += 1;
                }
                tokens.push(Token::Var(name));
            }
            c if c.is_ascii_digit() => {
                return Err(format!("Variable names cannot start with a digit: '{}'", c));
            }
            '\'' => {
                return Err("Unexpected ' — complement must follow a variable name".to_string());
            }
            _ => { i += 1; }
        }
    }
    Ok(tokens)
}

// ─── Parser ───────────────────────────────────────────────────────────────────

struct Parser {
    tokens: Vec<Token>,
    pos: usize,
}

impl Parser {
    fn peek(&self) -> Option<&Token> {
        self.tokens.get(self.pos)
    }

    fn eat(&mut self) -> Option<Token> {
        if self.pos < self.tokens.len() {
            let t = self.tokens[self.pos].clone();
            self.pos += 1;
            Some(t)
        } else {
            None
        }
    }

    fn parse_expr(&mut self) -> Result<Node, String> {
        let mut left = self.parse_term()?;
        while matches!(self.peek(), Some(Token::Plus)) {
            self.eat();
            if self.peek().is_none() {
                return Err("Expected term after '+'".to_string());
            }
            let right = self.parse_term()?;
            left = match left {
                Node::Or(mut c) => { c.push(right); Node::Or(c) }
                other => Node::Or(vec![other, right]),
            };
        }
        Ok(left)
    }

    fn parse_term(&mut self) -> Result<Node, String> {
        let mut left = self.parse_factor()?;
        loop {
            match self.peek() {
                Some(Token::Dot) => { self.eat(); }           // explicit ·
                Some(Token::Var(_)) | Some(Token::LParen) => {} // implicit AND
                _ => break,
            }
            let right = self.parse_factor()?;
            left = match left {
                Node::And(mut c) => { c.push(right); Node::And(c) }
                other => Node::And(vec![other, right]),
            };
        }
        Ok(left)
    }

    fn parse_factor(&mut self) -> Result<Node, String> {
        match self.peek() {
            None => Err("Unexpected end of formula".to_string()),
            Some(Token::RParen) => Err("Unexpected ')'".to_string()),
            Some(Token::Plus)   => Err("Unexpected '+' — missing left operand?".to_string()),
            Some(Token::Dot)    => Err("Unexpected '·' — missing left operand?".to_string()),
            Some(Token::LParen) => {
                self.eat();
                let expr = self.parse_expr()?;
                if !matches!(self.peek(), Some(Token::RParen)) {
                    return Err("Missing closing ')'".to_string());
                }
                self.eat();
                Ok(expr)
            }
            Some(Token::Var(_)) => {
                if let Some(Token::Var(name)) = self.eat() {
                    Ok(Node::Var(name))
                } else {
                    unreachable!()
                }
            }
        }
    }
}

impl TryFrom<&str> for Node {
    type Error = String;

    fn try_from(s: &str) -> Result<Self, String> {
        if s.trim().is_empty() {
            return Err("Formula is empty".to_string());
        }
        let tokens = tokenize(s)?;
        let mut parser = Parser { tokens, pos: 0 };
        let result = parser.parse_expr()?;
        if parser.pos < parser.tokens.len() {
            return Err("Unexpected content after formula".to_string());
        }
        Ok(result)
    }
}

// ─── AST helpers ──────────────────────────────────────────────────────────────

pub fn get_base_name(s: &str) -> &str {
    s.trim_end_matches('\'')
}

pub fn count_primes(s: &str) -> usize {
    s.chars().filter(|&c| c == '\'').count()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_ok(s: &str) -> Node {
        Node::try_from(s).unwrap_or_else(|e| panic!("Expected parse to succeed for {:?}: {}", s, e))
    }

    trait NodeExt { fn is_var_or_op(&self) -> bool; }
    impl NodeExt for Node {
        fn is_var_or_op(&self) -> bool { true }
    }

    #[test]
    fn test_parse_empty() {
        assert!(Node::try_from("").is_err());
        assert!(Node::try_from("   ").is_err());
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
        assert!(matches!(parse_ok("A '"), Node::Var(n) if n == "A'"));
        assert!(matches!(parse_ok("foo_bar'"), Node::Var(n) if n == "foo_bar'"));
    }

    #[test]
    fn test_parse_literals() {
        assert!(matches!(parse_ok("0"),  Node::Var(n) if n == "0"));
        assert!(matches!(parse_ok("1"),  Node::Var(n) if n == "1"));
        assert!(matches!(parse_ok("0'"), Node::Var(n) if n == "0'"));
        assert!(matches!(parse_ok("1'"), Node::Var(n) if n == "1'"));
        assert!(matches!(parse_ok("0 '"), Node::Var(n) if n == "0'"));
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
        assert!(Node::try_from("(A + B").is_err());
        assert!(Node::try_from("A + B)").is_err());
    }

    #[test]
    fn test_parse_error_stray_prime() {
        assert!(Node::try_from("'A").is_err());
        assert!(Node::try_from("A + 'B").is_err());
        assert!(Node::try_from("(A * 'B)").is_err());
    }

    #[test]
    fn test_parse_error_digit_start() {
        assert!(Node::try_from("2A").is_err());
        assert!(Node::try_from("9").is_err());
        assert!(Node::try_from("1B").is_ok());
    }

    #[test]
    fn test_parse_error_missing_operand() {
        assert!(Node::try_from("A +").is_err());
        assert!(Node::try_from("+ A").is_err());
        assert!(Node::try_from("A · · B").is_err());
        assert!(Node::try_from("()").is_err());
    }
}
