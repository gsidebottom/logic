use std::collections::{BTreeSet, HashMap, HashSet};

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

fn tokenize(s: &str) -> Vec<Token> {
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
            c if c.is_alphanumeric() => {
                let mut name = c.to_string();
                i += 1;
                while i < chars.len() && chars[i] == '\'' {
                    name.push('\'');
                    i += 1;
                }
                tokens.push(Token::Var(name));
            }
            _ => { i += 1; }
        }
    }
    tokens
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
        while matches!(self.peek(), Some(Token::Dot)) {
            self.eat();
            if self.peek().is_none() {
                return Err("Expected factor after '·'".to_string());
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

fn parse(s: &str) -> Result<Node, String> {
    if s.trim().is_empty() {
        return Err("Formula is empty".to_string());
    }
    let tokens = tokenize(s);
    let mut parser = Parser { tokens, pos: 0 };
    let result = parser.parse_expr()?;
    if parser.pos < parser.tokens.len() {
        return Err("Unexpected content after formula".to_string());
    }
    Ok(result)
}

// ─── Evaluator ────────────────────────────────────────────────────────────────

fn get_base_name(s: &str) -> &str {
    s.trim_end_matches('\'')
}

fn count_primes(s: &str) -> usize {
    s.chars().filter(|&c| c == '\'').count()
}

fn extract_vars(node: &Node) -> BTreeSet<String> {
    let mut set = BTreeSet::new();
    match node {
        Node::Var(n) => { set.insert(get_base_name(n).to_string()); }
        Node::And(c) | Node::Or(c) => {
            for child in c { set.extend(extract_vars(child)); }
        }
    }
    set
}

fn evaluate(node: &Node, asgn: &HashMap<String, u8>) -> u8 {
    match node {
        Node::Var(name) => {
            let base = get_base_name(name);
            let val = *asgn.get(base).unwrap_or(&0);
            if count_primes(name) % 2 == 1 { 1 - val } else { val }
        }
        Node::And(c) => if c.iter().all(|ch| evaluate(ch, asgn) == 1) { 1 } else { 0 },
        Node::Or(c)  => if c.iter().any(|ch| evaluate(ch, asgn) == 1) { 1 } else { 0 },
    }
}

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

// ─── Public API ───────────────────────────────────────────────────────────────

pub fn simplify(formula: &str) -> Result<String, String> {
    let ast = parse(formula)?;
    let vars: Vec<String> = extract_vars(&ast).into_iter().collect();
    let n = vars.len();

    if n == 0 { return Ok(formula.to_string()); }
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
