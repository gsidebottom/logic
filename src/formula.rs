use std::collections::{BTreeSet, HashMap};

// ─── AST ──────────────────────────────────────────────────────────────────────

#[derive(Clone, Debug)]
pub enum Node {
    Var(String),
    And(Vec<Node>),
    Or(Vec<Node>),
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

pub fn parse(s: &str) -> Result<Node, String> {
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

// ─── AST helpers ──────────────────────────────────────────────────────────────

pub fn get_base_name(s: &str) -> &str {
    s.trim_end_matches('\'')
}

pub fn count_primes(s: &str) -> usize {
    s.chars().filter(|&c| c == '\'').count()
}

pub fn extract_vars(node: &Node) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    match node {
        Node::Var(n) => {
            let base = get_base_name(n);
            if base != "0" && base != "1" { set.insert(base.to_string()); }
        }
        Node::And(c) | Node::Or(c) => {
            for child in c { set.extend(extract_vars(child)); }
        }
    }
    set
}

pub fn evaluate(node: &Node, asgn: &HashMap<String, u8>) -> u8 {
    match node {
        Node::Var(name) => {
            let base = get_base_name(name);
            if base == "0" || base == "1" {
                let val = if base == "1" { 1u8 } else { 0u8 };
                return if count_primes(name) % 2 == 1 { 1 - val } else { val };
            }
            let val = *asgn.get(base).unwrap_or(&0);
            if count_primes(name) % 2 == 1 { 1 - val } else { val }
        }
        Node::And(c) => if c.iter().all(|ch| evaluate(ch, asgn) == 1) { 1 } else { 0 },
        Node::Or(c)  => if c.iter().any(|ch| evaluate(ch, asgn) == 1) { 1 } else { 0 },
    }
}
