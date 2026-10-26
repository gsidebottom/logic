//! slpopt: the first-order rounding model of a <4x4x4:48> program (L, R and P straight-line
//! programs in PLinOpt syntax, evaluated as written, as gen_kernels.py fuses them), and a search
//! for programs that add less rounding error.
//!
//! The model is matmul/dps48/gamma/slp_errmodel.py's, ported for speed: every addition, and
//! every scaling by a constant that is not a power of two, rounds, with error proportional to the
//! exact value rounded; the errors are independent; the inputs are i.i.d. with unit variance, so the
//! products M_i = X_i Y_i have covariance G = (L L^T) o (R R^T) and every intermediate's size,
//! cancellation included, is an exact second moment.
//!
//!   slpopt model NAME PREFIX [NAME PREFIX ...]     score PREFIX_{L,R,P}.slp (the Python table)
//!   slpopt dagmodel NAME PREFIX [...]              the same through the DAG representation
//!   slpopt search --scheme PREFIX --matrix L|R|P --out FILE.slp [--init FILE.slp]
//!                 [--fixed PREFIX] [--steps N] [--restarts R] [--seed S] [--threads T]
//!     simulated annealing over programs of one matrix, the other two matrices' programs fixed
//!     (PREFIX_{X}.slp of --fixed, default --scheme), objective the model's worst output error
use rayon::prelude::*;
use std::collections::HashMap;

// ------------------------------------------------------------------ text programs, the model

/// A value in a program: a constant, or a linear form over the inputs with the first-order
/// error terms of the roundings that reach it.
#[derive(Clone, Debug)]
enum Val {
    Const(f64),
    Lin(Lin),
}

#[derive(Clone, Debug)]
struct Lin {
    c: Vec<f64>,              // coefficients over the inputs
    w: HashMap<usize, f64>,   // rounding -> weight of its error in this value
    d: HashMap<usize, usize>, // input -> longest chain of roundings from it
}

/// A parsed straight-line program: the rounded values (their coefficient vectors) and the
/// environment of named values.
struct Program {
    nin: usize,
    rounded: Vec<Vec<f64>>,
    env: HashMap<String, Lin>,
}

fn is_pow2(c: f64) -> bool {
    let a = c.abs();
    a != 0.0 && a.is_finite() && a.log2().fract() == 0.0
}

#[derive(Clone, Debug, PartialEq)]
enum Tok {
    Num(f64),
    Id(String),
    Op(char),
}

fn tokenize(s: &str) -> Vec<Tok> {
    let b = s.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        let ch = b[i] as char;
        if ch.is_whitespace() {
            i += 1;
        } else if ch.is_ascii_digit() || (ch == '.' && i + 1 < b.len() && (b[i + 1] as char).is_ascii_digit()) {
            let st = i;
            while i < b.len() && ((b[i] as char).is_ascii_digit() || b[i] == b'.') {
                i += 1;
            }
            if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
                let save = i;
                i += 1;
                if i < b.len() && (b[i] == b'-' || b[i] == b'+') {
                    i += 1;
                }
                if i < b.len() && (b[i] as char).is_ascii_digit() {
                    while i < b.len() && (b[i] as char).is_ascii_digit() {
                        i += 1;
                    }
                } else {
                    i = save;
                }
            }
            out.push(Tok::Num(s[st..i].parse().unwrap_or_else(|_| panic!("number {}", &s[st..i]))));
        } else if ch.is_ascii_alphabetic() || ch == '_' {
            let st = i;
            while i < b.len() && ((b[i] as char).is_ascii_alphanumeric() || b[i] == b'_') {
                i += 1;
            }
            out.push(Tok::Id(s[st..i].to_string()));
        } else {
            out.push(Tok::Op(ch));
            i += 1;
        }
    }
    out
}

struct Parser<'a> {
    toks: Vec<Tok>,
    k: usize,
    prog: &'a mut Program,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.k)
    }
    fn eat(&mut self) -> Tok {
        self.k += 1;
        self.toks[self.k - 1].clone()
    }
    fn rounding(&mut self, c: Vec<f64>, mut w: HashMap<usize, f64>, d: &HashMap<usize, usize>) -> Lin {
        let id = self.prog.rounded.len();
        self.prog.rounded.push(c.clone());
        w.insert(id, 1.0);
        Lin { c, w, d: d.iter().map(|(&x, &n)| (x, n + 1)).collect() }
    }
    fn expr(&mut self) -> Val {
        let mut v = self.term();
        while let Some(Tok::Op(op)) = self.peek() {
            let op = *op;
            if op != '+' && op != '-' {
                break;
            }
            self.eat();
            let u = self.term();
            let s = if op == '+' { 1.0 } else { -1.0 };
            v = match (v, u) {
                (Val::Const(a), Val::Const(b)) => Val::Const(a + s * b),
                // an exact zero term (PLinOpt's LU method writes o:=0+...): no rounding
                (Val::Const(a), Val::Lin(b)) if a == 0.0 => Val::Lin(if s < 0.0 {
                    Lin { c: b.c.iter().map(|x| -x).collect(), w: b.w.iter().map(|(r, x)| (*r, -x)).collect(), d: b.d }
                } else {
                    b
                }),
                (Val::Lin(a), Val::Const(b)) if b == 0.0 => Val::Lin(a),
                (Val::Lin(a), Val::Lin(b)) => {
                    let c: Vec<f64> = a.c.iter().zip(&b.c).map(|(x, y)| x + s * y).collect();
                    let mut w = a.w.clone();
                    for (r, x) in &b.w {
                        *w.entry(*r).or_insert(0.0) += s * x;
                    }
                    let mut d = a.d.clone();
                    for (x, n) in &b.d {
                        let e = d.entry(*x).or_insert(0);
                        *e = (*e).max(*n);
                    }
                    Val::Lin(self.rounding(c, w, &d))
                }
                _ => panic!("adding a constant to a variable"),
            };
        }
        v
    }
    fn term(&mut self) -> Val {
        let mut v = self.factor();
        while let Some(Tok::Op(op)) = self.peek() {
            let op = *op;
            if op != '*' && op != '/' {
                break;
            }
            self.eat();
            let u = self.factor();
            v = match (v, u) {
                (Val::Const(a), Val::Const(b)) => Val::Const(if op == '*' { a * b } else { a / b }),
                (Val::Lin(a), Val::Const(b)) => self.scale(a, if op == '*' { b } else { 1.0 / b }),
                (Val::Const(a), Val::Lin(b)) if op == '*' => self.scale(b, a),
                _ => panic!("not a linear program"),
            };
        }
        v
    }
    fn scale(&mut self, v: Lin, c: f64) -> Val {
        let out = Lin {
            c: v.c.iter().map(|x| x * c).collect(),
            w: v.w.iter().map(|(r, x)| (*r, x * c)).collect(),
            d: v.d.clone(),
        };
        if is_pow2(c) { Val::Lin(out) } else { Val::Lin(self.rounding(out.c.clone(), out.w.clone(), &out.d)) }
    }
    fn factor(&mut self) -> Val {
        match self.eat() {
            Tok::Op('-') => match self.factor() {
                Val::Const(a) => Val::Const(-a),
                Val::Lin(a) => Val::Lin(Lin {
                    c: a.c.iter().map(|x| -x).collect(),
                    w: a.w.iter().map(|(r, x)| (*r, -x)).collect(),
                    d: a.d,
                }),
            },
            Tok::Op('(') => {
                let v = self.expr();
                assert_eq!(self.eat(), Tok::Op(')'), "missing )");
                v
            }
            Tok::Num(x) => Val::Const(x),
            Tok::Id(name) => {
                if let Some(v) = self.prog.env.get(&name) {
                    Val::Lin(v.clone())
                } else if let Some(k) = name.strip_prefix('i').and_then(|t| t.parse::<usize>().ok()) {
                    let mut c = vec![0.0; self.prog.nin];
                    c[k] = 1.0;
                    Val::Lin(Lin { c, w: HashMap::new(), d: HashMap::from([(k, 0)]) })
                } else {
                    panic!("unknown variable {name}")
                }
            }
            t => panic!("unexpected token {t:?}"),
        }
    }
}

/// The per-output data of a program needed by the model
struct Pass {
    c: Vec<Vec<f64>>,     // outputs as coefficient rows over the inputs
    w: Vec<Vec<f64>>,     // outputs x roundings: weights
    s: Vec<f64>,          // roundings: |value|^2 with identity input covariance (L, R) -- P uses G
    nodes: Vec<Vec<f64>>, // roundings: coefficient vectors
    depth: Vec<HashMap<usize, usize>>,
}

impl Program {
    fn parse(path: &str, nin: usize) -> Program {
        let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let mut prog = Program { nin, rounded: Vec::new(), env: HashMap::new() };
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') || !line.contains(":=") {
                continue;
            }
            let (lhs, rhs) = line.trim_end_matches(';').split_once(":=").unwrap();
            let toks = tokenize(rhs);
            let v = {
                let mut p = Parser { toks, k: 0, prog: &mut prog };
                p.expr()
            };
            match v {
                Val::Lin(l) => {
                    prog.env.insert(lhs.trim().to_string(), l);
                }
                Val::Const(_) => panic!("{path}: constant assignment {line}"),
            }
        }
        prog
    }

    fn pass(&self, n: usize) -> Pass {
        let nr = self.rounded.len();
        let mut c = Vec::with_capacity(n);
        let mut w = Vec::with_capacity(n);
        let mut depth = Vec::with_capacity(n);
        for j in 0..n {
            let v = self.env.get(&format!("o{j}")).unwrap_or_else(|| panic!("output o{j} missing"));
            c.push(v.c.clone());
            let mut row = vec![0.0; nr];
            for (r, x) in &v.w {
                row[*r] = *x;
            }
            w.push(row);
            depth.push(v.d.clone());
        }
        let s = self.rounded.iter().map(|v| v.iter().map(|x| x * x).sum()).collect();
        Pass { c, w, s, nodes: self.rounded.clone(), depth }
    }
}

// ------------------------------------------------------------------ the scheme and the model

struct Scheme {
    l: Vec<Vec<f64>>,  // 48 x 16
    r: Vec<Vec<f64>>,  // 48 x 16
    p: Vec<Vec<f64>>,  // 16 x 48
    gl: Vec<Vec<f64>>, // L L^T
    gr: Vec<Vec<f64>>, // R R^T
    g: Vec<Vec<f64>>,  // gl o gr: covariance of the products
}

fn gram(a: &[Vec<f64>]) -> Vec<Vec<f64>> {
    let n = a.len();
    let mut g = vec![vec![0.0; n]; n];
    for i in 0..n {
        for k in i..n {
            let s: f64 = a[i].iter().zip(&a[k]).map(|(x, y)| x * y).sum();
            g[i][k] = s;
            g[k][i] = s;
        }
    }
    g
}

impl Scheme {
    fn new(l: Vec<Vec<f64>>, r: Vec<Vec<f64>>, p: Vec<Vec<f64>>) -> Scheme {
        let gl = gram(&l);
        let gr = gram(&r);
        let g: Vec<Vec<f64>> = gl.iter().zip(&gr).map(|(a, b)| a.iter().zip(b).map(|(x, y)| x * y).collect()).collect();
        for j in 0..p.len() {
            let mut e = 0.0;
            for i in 0..48 {
                if p[j][i] != 0.0 {
                    for k in 0..48 {
                        e += p[j][i] * g[i][k] * p[j][k];
                    }
                }
            }
            assert!((e - 4.0).abs() < 1e-9, "not a <4x4x4:48> scheme: output {j} has second moment {e}");
        }
        Scheme { l, r, p, gl, gr, g }
    }
    fn from_sms(prefix: &str) -> Scheme {
        Scheme::new(read_sms(&format!("{prefix}_L.sms")), read_sms(&format!("{prefix}_R.sms")), read_sms(&format!("{prefix}_P.sms")))
    }
    /// v^T G v
    fn quad(&self, v: &[f64]) -> f64 {
        let mut s = 0.0;
        for i in 0..48 {
            if v[i] != 0.0 {
                let gi = &self.g[i];
                let mut acc = 0.0;
                for k in 0..48 {
                    acc += gi[k] * v[k];
                }
                s += v[i] * acc;
            }
        }
        s
    }
}

fn read_sms(path: &str) -> Vec<Vec<f64>> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut lines = text.lines().map(str::trim).filter(|l| !l.is_empty() && !l.starts_with('#'));
    let head: Vec<usize> = lines.next().unwrap().split_whitespace().take(2).map(|x| x.parse().unwrap()).collect();
    let mut m = vec![vec![0.0; head[1]]; head[0]];
    for l in lines {
        let f: Vec<&str> = l.split_whitespace().collect();
        let (i, j): (usize, usize) = (f[0].parse().unwrap(), f[1].parse().unwrap());
        if i == 0 {
            break;
        }
        let v = match f[2].split_once('/') {
            Some((p, q)) => p.parse::<f64>().unwrap() / q.parse::<f64>().unwrap(),
            None => f[2].parse().unwrap(),
        };
        m[i - 1][j - 1] = v;
    }
    m
}

/// cov = W diag(s) W^T
fn error_cov(w: &[Vec<f64>], s: &[f64]) -> Vec<Vec<f64>> {
    let n = w.len();
    let mut cov = vec![vec![0.0; n]; n];
    for i in 0..n {
        for k in i..n {
            let mut acc = 0.0;
            for (r, &sr) in s.iter().enumerate() {
                acc += w[i][r] * sr * w[k][r];
            }
            cov[i][k] = acc;
            cov[k][i] = acc;
        }
    }
    cov
}

/// The error the L pass adds to each output: sum_{ik} P_ji P_jk covX_ik GR_ik (and R's with GL)
fn lr_part(sch: &Scheme, cov: &[Vec<f64>], other_gram: &[Vec<f64>]) -> Vec<f64> {
    let mut out = vec![0.0; 16];
    for j in 0..16 {
        let pj = &sch.p[j];
        for i in 0..48 {
            if pj[i] == 0.0 {
                continue;
            }
            for k in 0..48 {
                if pj[k] != 0.0 {
                    out[j] += pj[i] * pj[k] * cov[i][k] * other_gram[i][k];
                }
            }
        }
    }
    out
}

/// The error the P pass adds to each output, its count of roundings and their mean size
fn p_part(sch: &Scheme, w: &[Vec<f64>], nodes: &[Vec<f64>]) -> (Vec<f64>, Vec<f64>, Vec<f64>) {
    let size2: Vec<f64> = nodes.iter().map(|v| sch.quad(v)).collect();
    let mut pe = vec![0.0; 16];
    let mut count = vec![0.0; 16];
    let mut size = vec![0.0; 16];
    for j in 0..16 {
        let mut n = 0.0;
        for (k, &x) in w[j].iter().enumerate() {
            if x.abs() > 1e-12 {
                n += 1.0;
                pe[j] += x * x * size2[k];
            }
        }
        count[j] = n;
        size[j] = if n > 0.0 { (pe[j] / 4.0 / n).sqrt() } else { 0.0 };
    }
    (pe, count, size)
}

struct Analysis {
    lr: f64,
    p: f64,
    worst: f64,
    amp: f64,
    count: f64,
    size: f64,
    chain: usize,
    roundings: (usize, usize, usize),
    lr_l: Vec<f64>, // per output, the L pass's part
    lr_r: Vec<f64>,
    pe: Vec<f64>,
}

fn rel(v: f64) -> f64 {
    (v / 4.0).sqrt()
}
fn mean(v: &[f64]) -> f64 {
    v.iter().sum::<f64>() / v.len() as f64
}

fn summarize(sch: &Scheme, lr_l: Vec<f64>, lr_r: Vec<f64>, pe: Vec<f64>, count: Vec<f64>, size: Vec<f64>, chain: usize, roundings: (usize, usize, usize)) -> Analysis {
    let lr: Vec<f64> = lr_l.iter().zip(&lr_r).map(|(a, b)| a + b).collect();
    let amp = (0..16)
        .map(|j| (0..48).map(|i| sch.p[j][i] * sch.p[j][i] * sch.g[i][i]).sum::<f64>().sqrt() / 2.0)
        .fold(0.0, f64::max);
    Analysis {
        lr: mean(&lr.iter().map(|&v| rel(v)).collect::<Vec<_>>()),
        p: mean(&pe.iter().map(|&v| rel(v)).collect::<Vec<_>>()),
        worst: lr.iter().zip(&pe).map(|(a, b)| rel(a + b)).fold(0.0, f64::max),
        amp,
        count: mean(&count),
        size: mean(&size),
        chain,
        roundings,
        lr_l,
        lr_r,
        pe,
    }
}

fn analyse(prefix: &str) -> Analysis {
    let pl = Program::parse(&format!("{prefix}_L.slp"), 16).pass(48);
    let pr = Program::parse(&format!("{prefix}_R.slp"), 16).pass(48);
    let pp = Program::parse(&format!("{prefix}_P.slp"), 48).pass(16);
    let sch = Scheme::new(pl.c.clone(), pr.c.clone(), pp.c.clone());
    let lr_l = lr_part(&sch, &error_cov(&pl.w, &pl.s), &sch.gr);
    let lr_r = lr_part(&sch, &error_cov(&pr.w, &pr.s), &sch.gl);
    let (pe, count, size) = p_part(&sch, &pp.w, &pp.nodes);
    let depth_l: Vec<usize> = pl.depth.iter().map(|d| *d.values().max().unwrap_or(&0)).collect();
    let depth_r: Vec<usize> = pr.depth.iter().map(|d| *d.values().max().unwrap_or(&0)).collect();
    let chain = pp.depth.iter().flat_map(|d| d.iter().map(|(&i, &n)| depth_l[i] + depth_r[i] + n)).max().unwrap_or(0);
    summarize(&sch, lr_l, lr_r, pe, count, size, chain, (pl.nodes.len(), pr.nodes.len(), pp.nodes.len()))
}

fn print_table_head() {
    println!("{:34} {:>5} {:>5} {:>6} {:>5}   count  size   chain   roundings L/R/P", "program", "L+R", "P", "worst", "amp");
}
fn print_row(name: &str, a: &Analysis) {
    println!(
        "{:34} {:5.2} {:5.2} {:6.2} {:5.2}   {:5.1} {:5.2}    {:3}    {}/{}/{}",
        name, a.lr, a.p, a.worst, a.amp, a.count, a.size, a.chain, a.roundings.0, a.roundings.1, a.roundings.2
    );
}

// ------------------------------------------------------------------ programs as DAGs

/// A program for one matrix as a DAG of linear nodes: inputs, sums of two nodes with signs, and
/// scalings by a constant.  Sums round; scalings round unless by a power of two.  Operand
/// indices may point anywhere (moves append nodes); evaluation orders the nodes topologically.
#[derive(Clone, Debug)]
enum Node {
    In(usize),
    Add { a: usize, sa: f64, b: usize, sb: f64 },
    Scale { a: usize, c: f64 },
}

#[derive(Clone, Debug)]
struct Dag {
    nin: usize,
    nodes: Vec<Node>,
    outs: Vec<(usize, f64)>, // output j = coef * node (coef is +-1 or +- a power of two)
}

#[derive(Clone, Copy)]
enum Term {
    Const(f64),
    Var(usize, f64),
}

struct DagParser<'a> {
    toks: Vec<Tok>,
    k: usize,
    dag: &'a mut Dag,
    env: &'a HashMap<String, (usize, f64)>,
}

impl Dag {
    fn push(&mut self, n: Node) -> usize {
        self.nodes.push(n);
        self.nodes.len() - 1
    }
    /// coef * node as a (node, sign) pair, creating a scaling node if |coef| != 1
    fn signed(&mut self, node: usize, coef: f64) -> (usize, f64) {
        if coef.abs() == 1.0 {
            (node, coef)
        } else {
            let s = self.push(Node::Scale { a: node, c: coef.abs() });
            (s, coef.signum())
        }
    }

    fn parse(path: &str, nin: usize) -> Dag {
        let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
        let mut dag = Dag { nin, nodes: (0..nin).map(Node::In).collect(), outs: Vec::new() };
        let mut env: HashMap<String, (usize, f64)> = HashMap::new();
        let mut outs: HashMap<usize, (usize, f64)> = HashMap::new();
        for line in text.lines() {
            let line = line.trim();
            if line.is_empty() || line.starts_with('#') || !line.contains(":=") {
                continue;
            }
            let (lhs, rhs) = line.trim_end_matches(';').split_once(":=").unwrap();
            let lhs = lhs.trim().to_string();
            let t = {
                let mut p = DagParser { toks: tokenize(rhs), k: 0, dag: &mut dag, env: &env };
                p.expr()
            };
            let (node, coef) = match t {
                Term::Var(n, c) => (n, c),
                Term::Const(_) => panic!("{path}: constant assignment {line}"),
            };
            if let Some(j) = lhs.strip_prefix('o').and_then(|s| s.parse::<usize>().ok()) {
                let (n, c) = if coef.abs() == 1.0 || is_pow2(coef) { (node, coef) } else { dag.signed(node, coef) };
                outs.insert(j, (n, c));
            }
            env.insert(lhs, (node, coef));
        }
        let nout = outs.keys().max().map(|m| m + 1).unwrap_or(0);
        dag.outs = (0..nout).map(|j| *outs.get(&j).unwrap_or_else(|| panic!("output o{j} missing"))).collect();
        dag
    }

    /// Every output as a direct sum of its matrix row, built greedily (the pair of terms with
    /// the smallest sum first), for a start without any program
    fn direct(nin: usize, rows: &[Vec<f64>], quad: &dyn Fn(&[f64]) -> f64) -> Dag {
        let mut dag = Dag { nin, nodes: (0..nin).map(Node::In).collect(), outs: Vec::new() };
        for row in rows {
            let mut terms: Vec<(usize, f64)> = Vec::new();
            for (k, &c) in row.iter().enumerate() {
                if c != 0.0 {
                    terms.push(dag.signed(k, c));
                }
            }
            let (node, coef) = dag.build_greedy(&terms, quad);
            dag.outs.push((node, coef));
        }
        dag
    }

    fn form_of(&self, forms: &[Vec<f64>], node: usize, sign: f64) -> Vec<f64> {
        forms[node].iter().map(|x| sign * x).collect()
    }

    /// Combine terms (node, sign) into a tree, always merging the pair whose sum is smallest
    fn build_greedy(&mut self, terms: &[(usize, f64)], quad: &dyn Fn(&[f64]) -> f64) -> (usize, f64) {
        if terms.len() == 1 {
            return terms[0];
        }
        let forms = self.forms();
        let mut cur: Vec<(usize, f64, Vec<f64>)> = terms.iter().map(|&(n, s)| (n, s, self.form_of(&forms, n, s))).collect();
        while cur.len() > 1 {
            let mut best = (f64::INFINITY, 0, 1);
            for a in 0..cur.len() {
                for b in a + 1..cur.len() {
                    let sum: Vec<f64> = cur[a].2.iter().zip(&cur[b].2).map(|(x, y)| x + y).collect();
                    let q = quad(&sum);
                    if q < best.0 {
                        best = (q, a, b);
                    }
                }
            }
            let (_, a, b) = best;
            let (na, sa, fa) = cur[a].clone();
            let (nb, sb, fb) = cur[b].clone();
            let n = self.push(Node::Add { a: na, sa, b: nb, sb });
            let f: Vec<f64> = fa.iter().zip(&fb).map(|(x, y)| x + y).collect();
            cur.remove(b);
            cur.remove(a);
            cur.push((n, 1.0, f));
        }
        (cur[0].0, cur[0].1)
    }

    /// Combine terms into a random binary tree
    fn build_random(&mut self, terms: &[(usize, f64)], rng: &mut Rng) -> (usize, f64) {
        let mut cur: Vec<(usize, f64)> = terms.to_vec();
        while cur.len() > 1 {
            let a = rng.below(cur.len());
            let mut b = rng.below(cur.len() - 1);
            if b >= a {
                b += 1;
            }
            let (na, sa) = cur[a];
            let (nb, sb) = cur[b];
            let n = self.push(Node::Add { a: na, sa, b: nb, sb });
            let (hi, lo) = if a > b { (a, b) } else { (b, a) };
            cur.remove(hi);
            cur.remove(lo);
            cur.push((n, 1.0));
        }
        cur[0]
    }

    /// Topological order of the nodes reachable from the outputs (inputs first)
    fn order(&self) -> Vec<usize> {
        let n = self.nodes.len();
        let mut state = vec![0u8; n]; // 0 new, 1 on stack, 2 done
        let mut order = Vec::with_capacity(n);
        let mut stack: Vec<(usize, bool)> = Vec::new();
        for &(root, _) in &self.outs {
            stack.push((root, false));
            while let Some((v, back)) = stack.pop() {
                if back {
                    state[v] = 2;
                    order.push(v);
                    continue;
                }
                if state[v] != 0 {
                    continue;
                }
                state[v] = 1;
                stack.push((v, true));
                match self.nodes[v] {
                    Node::In(_) => {}
                    Node::Add { a, b, .. } => {
                        if state[b] == 0 {
                            stack.push((b, false));
                        }
                        if state[a] == 0 {
                            stack.push((a, false));
                        }
                    }
                    Node::Scale { a, .. } => {
                        if state[a] == 0 {
                            stack.push((a, false));
                        }
                    }
                }
            }
        }
        order
    }

    /// Linear forms of all nodes (unreachable ones empty)
    fn forms(&self) -> Vec<Vec<f64>> {
        let mut f: Vec<Vec<f64>> = vec![Vec::new(); self.nodes.len()];
        for &n in &self.order_all() {
            f[n] = match self.nodes[n] {
                Node::In(k) => {
                    let mut v = vec![0.0; self.nin];
                    v[k] = 1.0;
                    v
                }
                Node::Add { a, sa, b, sb } => f[a].iter().zip(&f[b]).map(|(x, y)| sa * x + sb * y).collect(),
                Node::Scale { a, c } => f[a].iter().map(|x| c * x).collect(),
            };
        }
        f
    }

    /// Topological order of all nodes (also the unreachable ones)
    fn order_all(&self) -> Vec<usize> {
        let n = self.nodes.len();
        let mut state = vec![0u8; n];
        let mut order = Vec::with_capacity(n);
        let mut stack: Vec<(usize, bool)> = Vec::new();
        for root in 0..n {
            if state[root] != 0 {
                continue;
            }
            stack.push((root, false));
            while let Some((v, back)) = stack.pop() {
                if back {
                    state[v] = 2;
                    order.push(v);
                    continue;
                }
                if state[v] != 0 {
                    continue;
                }
                state[v] = 1;
                stack.push((v, true));
                match self.nodes[v] {
                    Node::In(_) => {}
                    Node::Add { a, b, .. } => {
                        if state[b] == 0 {
                            stack.push((b, false));
                        }
                        if state[a] == 0 {
                            stack.push((a, false));
                        }
                    }
                    Node::Scale { a, .. } => {
                        if state[a] == 0 {
                            stack.push((a, false));
                        }
                    }
                }
            }
        }
        order
    }

    fn rounds(&self, n: usize) -> bool {
        match self.nodes[n] {
            Node::In(_) => false,
            Node::Add { .. } => true,
            Node::Scale { c, .. } => !is_pow2(c),
        }
    }

    /// Weights of every node in every output along a reverse topological order
    fn weights(&self, order: &[usize]) -> Vec<Vec<f64>> {
        let mut w = vec![vec![0.0; self.nodes.len()]; self.outs.len()];
        for (j, &(node, coef)) in self.outs.iter().enumerate() {
            let wj = &mut w[j];
            wj[node] += coef;
            for &n in order.iter().rev() {
                let wn = wj[n];
                if wn == 0.0 {
                    continue;
                }
                match self.nodes[n] {
                    Node::In(_) => {}
                    Node::Add { a, sa, b, sb } => {
                        wj[a] += sa * wn;
                        wj[b] += sb * wn;
                    }
                    Node::Scale { a, c } => wj[a] += c * wn,
                }
            }
        }
        w
    }

    /// Number of consumers of each node (outputs count as consumers)
    fn consumers(&self) -> Vec<usize> {
        let mut c = vec![0usize; self.nodes.len()];
        for n in &self.nodes {
            match *n {
                Node::In(_) => {}
                Node::Add { a, b, .. } => {
                    c[a] += 1;
                    c[b] += 1;
                }
                Node::Scale { a, .. } => c[a] += 1,
            }
        }
        for &(node, _) in &self.outs {
            c[node] += 1;
        }
        c
    }

    /// Drop unreachable nodes, renumber in topological order (inputs first)
    fn compact(&mut self) {
        let order = self.order();
        let mut map = vec![usize::MAX; self.nodes.len()];
        let mut nodes: Vec<Node> = Vec::with_capacity(order.len());
        for k in 0..self.nin {
            map[k] = k;
            nodes.push(Node::In(k));
        }
        for &n in &order {
            if n < self.nin {
                continue;
            }
            map[n] = nodes.len();
            nodes.push(match self.nodes[n] {
                Node::In(k) => Node::In(k),
                Node::Add { a, sa, b, sb } => Node::Add { a: map[a], sa, b: map[b], sb },
                Node::Scale { a, c } => Node::Scale { a: map[a], c },
            });
        }
        for o in &mut self.outs {
            o.0 = map[o.0];
        }
        self.nodes = nodes;
    }

    /// The program as PLinOpt text (after compact): constants as rationals (*3/4, /2, *2)
    fn to_slp(&self) -> String {
        let name = |n: usize, nin: usize| if n < nin { format!("i{n}") } else { format!("t{}", n - nin) };
        let mut s = String::new();
        for (n, node) in self.nodes.iter().enumerate() {
            match *node {
                Node::In(_) => {}
                Node::Add { a, sa, b, sb } => {
                    let (na, nb) = (name(a, self.nin), name(b, self.nin));
                    let first = if sa < 0.0 { format!("-{na}") } else { na };
                    let op = if sb < 0.0 { '-' } else { '+' };
                    s.push_str(&format!("{}:={first}{op}{nb};\n", name(n, self.nin)));
                }
                Node::Scale { a, c } => {
                    s.push_str(&format!("{}:={}{};\n", name(n, self.nin), name(a, self.nin), scaling(c)));
                }
            }
        }
        for (j, &(node, coef)) in self.outs.iter().enumerate() {
            let na = name(node, self.nin);
            let sign = if coef < 0.0 { "-" } else { "" };
            s.push_str(&format!("o{j}:={sign}{na}{};\n", scaling(coef.abs())));
        }
        s
    }
}

/// "*p/q", "/q", "*p" or "" for a positive rational scaling (dyadic, else a small fraction)
fn scaling(c: f64) -> String {
    if c == 1.0 {
        return String::new();
    }
    let (mut p, mut q): (i64, i64) = (0, 0);
    for k in 0..=30 {
        let d = (1u64 << k) as f64;
        if (c * d).fract() == 0.0 && (c * d).abs() < 9e15 {
            p = (c * d) as i64;
            q = d as i64;
            break;
        }
    }
    if q == 0 {
        // continued fraction with a bounded denominator
        let (mut h0, mut h1, mut k0, mut k1, mut x) = (0i64, 1i64, 1i64, 0i64, c);
        for _ in 0..40 {
            let a = x.floor();
            let (h2, k2) = (a as i64 * h1 + h0, a as i64 * k1 + k0);
            if k2 > 1_000_000 {
                break;
            }
            h0 = h1;
            h1 = h2;
            k0 = k1;
            k1 = k2;
            if ((h1 as f64 / k1 as f64) - c).abs() < 1e-12 {
                break;
            }
            x = 1.0 / (x - a);
        }
        p = h1;
        q = k1;
    }
    let g = gcd(p.abs(), q);
    let (p, q) = (p / g, q / g);
    if q == 1 { format!("*{p}") } else if p == 1 { format!("/{q}") } else { format!("*{p}/{q}") }
}

fn gcd(a: i64, b: i64) -> i64 {
    if b == 0 { a.max(1) } else { gcd(b, a % b) }
}

impl Dag {

    /// The flat terms of the sum tree rooted at n: descend through Add nodes that have exactly
    /// one consumer; the leaves are everything else.  Returns (leaf, sign) pairs.
    fn flat_terms(&self, n: usize, sign: f64, consumers: &[usize], out: &mut Vec<(usize, f64)>) {
        match self.nodes[n] {
            Node::Add { a, sa, b, sb } if consumers[n] <= 1 || out.is_empty() => {
                // the root itself may be shared; its internal nodes must not be
                self.flat_terms_inner(a, sign * sa, consumers, out);
                self.flat_terms_inner(b, sign * sb, consumers, out);
            }
            _ => out.push((n, sign)),
        }
    }
    fn flat_terms_inner(&self, n: usize, sign: f64, consumers: &[usize], out: &mut Vec<(usize, f64)>) {
        match self.nodes[n] {
            Node::Add { a, sa, b, sb } if consumers[n] == 1 => {
                self.flat_terms_inner(a, sign * sa, consumers, out);
                self.flat_terms_inner(b, sign * sb, consumers, out);
            }
            _ => out.push((n, sign)),
        }
    }

    /// Replace the definition of node n by a tree over the given terms (the new root keeps n's
    /// identity, so its consumers are unchanged)
    fn redefine(&mut self, n: usize, terms: &[(usize, f64)], greedy: bool, quad: &dyn Fn(&[f64]) -> f64, rng: &mut Rng) {
        if terms.len() < 2 {
            return;
        }
        let (root, coef) = if greedy { self.build_greedy(terms, quad) } else { self.build_random(terms, rng) };
        // root is the last node pushed, an Add; move it into n
        debug_assert_eq!(coef, 1.0);
        let last = self.nodes.len() - 1;
        debug_assert_eq!(root, last);
        self.nodes[n] = self.nodes[last].clone();
        self.nodes[last] = Node::In(0); // dead
    }
}

impl<'a> DagParser<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.k)
    }
    fn eat(&mut self) -> Tok {
        self.k += 1;
        self.toks[self.k - 1].clone()
    }
    fn expr(&mut self) -> Term {
        let mut v = self.term();
        while let Some(Tok::Op(op)) = self.peek() {
            let op = *op;
            if op != '+' && op != '-' {
                break;
            }
            self.eat();
            let u = self.term();
            let s = if op == '+' { 1.0 } else { -1.0 };
            v = match (v, u) {
                (Term::Const(a), Term::Const(b)) => Term::Const(a + s * b),
                (Term::Const(a), Term::Var(nb, cb)) if a == 0.0 => Term::Var(nb, s * cb),
                (Term::Var(na, ca), Term::Const(b)) if b == 0.0 => Term::Var(na, ca),
                (Term::Var(na, ca), Term::Var(nb, cb)) => {
                    let (a, sa) = self.dag.signed(na, ca);
                    let (b, sb) = self.dag.signed(nb, s * cb);
                    Term::Var(self.dag.push(Node::Add { a, sa, b, sb }), 1.0)
                }
                _ => panic!("adding a constant to a variable"),
            };
        }
        v
    }
    fn term(&mut self) -> Term {
        let mut v = self.factor();
        while let Some(Tok::Op(op)) = self.peek() {
            let op = *op;
            if op != '*' && op != '/' {
                break;
            }
            self.eat();
            let u = self.factor();
            v = match (v, u) {
                (Term::Const(a), Term::Const(b)) => Term::Const(if op == '*' { a * b } else { a / b }),
                (Term::Var(n, c), Term::Const(b)) => Term::Var(n, if op == '*' { c * b } else { c / b }),
                (Term::Const(a), Term::Var(n, c)) if op == '*' => Term::Var(n, a * c),
                _ => panic!("not a linear program"),
            };
        }
        v
    }
    fn factor(&mut self) -> Term {
        match self.eat() {
            Tok::Op('-') => match self.factor() {
                Term::Const(a) => Term::Const(-a),
                Term::Var(n, c) => Term::Var(n, -c),
            },
            Tok::Op('(') => {
                let v = self.expr();
                assert_eq!(self.eat(), Tok::Op(')'), "missing )");
                v
            }
            Tok::Num(x) => Term::Const(x),
            Tok::Id(name) => {
                if let Some(&(n, c)) = self.env.get(&name) {
                    Term::Var(n, c)
                } else if let Some(k) = name.strip_prefix('i').and_then(|t| t.parse::<usize>().ok()) {
                    Term::Var(k, 1.0)
                } else {
                    panic!("unknown variable {name}")
                }
            }
            t => panic!("unexpected token {t:?}"),
        }
    }
}

// ------------------------------------------------------------------ the model on a DAG

#[derive(Clone, Copy, PartialEq, Debug)]
enum Which {
    L,
    R,
    P,
}

/// What a search for one matrix's program holds fixed: the scheme and the other passes' errors
struct Fixed {
    which: Which,
    sch: Scheme,
    other: Vec<f64>, // per output: the fixed passes' error (sum of the other two parts)
}

/// Per-output error of a DAG program for matrix `which`: (this pass's part, outputs' data)
fn dag_pass(sch: &Scheme, which: Which, dag: &Dag) -> (Vec<f64>, Vec<f64>, Vec<f64>) {
    let order = dag.order();
    let forms = dag.forms();
    let w = dag.weights(&order);
    let rounding: Vec<usize> = order.iter().cloned().filter(|&n| dag.rounds(n)).collect();
    match which {
        Which::P => {
            let size2: Vec<f64> = rounding.iter().map(|&n| sch.quad(&forms[n])).collect();
            let mut pe = vec![0.0; 16];
            let mut count = vec![0.0; 16];
            let mut size = vec![0.0; 16];
            for j in 0..16 {
                let mut cnt = 0.0;
                for (k, &n) in rounding.iter().enumerate() {
                    let x = w[j][n];
                    if x.abs() > 1e-12 {
                        cnt += 1.0;
                        pe[j] += x * x * size2[k];
                    }
                }
                count[j] = cnt;
                size[j] = if cnt > 0.0 { (pe[j] / 4.0 / cnt).sqrt() } else { 0.0 };
            }
            (pe, count, size)
        }
        Which::L | Which::R => {
            // cov_ik = sum_n w[i][n] w[k][n] |form_n|^2 over the roundings
            let s: Vec<f64> = rounding.iter().map(|&n| forms[n].iter().map(|x| x * x).sum()).collect();
            let wr: Vec<Vec<f64>> = (0..48).map(|i| rounding.iter().map(|&n| w[i][n]).collect()).collect();
            let cov = error_cov(&wr, &s);
            let part = lr_part(sch, &cov, if which == Which::L { &sch.gr } else { &sch.gl });
            (part, vec![0.0; 16], vec![0.0; 16])
        }
    }
}

/// Objective: a soft maximum of the outputs' errors (their 8-norm, which the annealing can
/// follow) and the worst output's error (what is reported)
fn objective(fixed: &Fixed, dag: &Dag) -> (f64, f64) {
    let (part, _, _) = dag_pass(&fixed.sch, fixed.which, dag);
    let tot: Vec<f64> = part.iter().zip(&fixed.other).map(|(a, b)| rel(a + b)).collect();
    let worst = tot.iter().cloned().fold(0.0, f64::max);
    let soft = tot.iter().map(|x| x.powi(8)).sum::<f64>().powf(1.0 / 8.0);
    (soft, worst)
}

/// The outputs' linear forms against the matrix rows: the move set must keep them
fn check_forms(dag: &Dag, rows: &[Vec<f64>]) -> Result<(), String> {
    let forms = dag.forms();
    for (j, &(node, coef)) in dag.outs.iter().enumerate() {
        for (k, &want) in rows[j].iter().enumerate() {
            let got = coef * forms[node][k];
            if (got - want).abs() > 1e-9 {
                return Err(format!("output {j}, input {k}: {got} instead of {want}"));
            }
        }
    }
    Ok(())
}

// ------------------------------------------------------------------ the search

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Rng {
        Rng(seed ^ 0x9e3779b97f4a7c15)
    }
    fn next(&mut self) -> u64 {
        // splitmix64
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
}

const MOVES: [&str; 5] = ["rebuild", "rotate", "share", "unshare", "cse"];

/// One random move on a copy of the DAG; None if the move did not apply.  Returns the move's
/// index in MOVES with the new DAG.
fn propose(dag: &Dag, fixed: &Fixed, rng: &mut Rng) -> Option<(usize, Dag)> {
    let mut d = dag.clone();
    let consumers = d.consumers();
    let adds: Vec<usize> = (0..d.nodes.len()).filter(|&n| matches!(d.nodes[n], Node::Add { .. }) && consumers[n] > 0).collect();
    if adds.is_empty() {
        return None;
    }
    let quad = |v: &[f64]| -> f64 {
        match fixed.which {
            Which::P => fixed.sch.quad(v),
            _ => v.iter().map(|x| x * x).sum(),
        }
    };
    let r = rng.unit();
    if r < 0.15 {
        // cse: a pair of leaves that co-occurs (same relative sign) in two or more sum trees
        // becomes a shared sum, as PLinOpt's optimizer would make it
        let roots: Vec<usize> = adds.iter().cloned().filter(|&n| consumers[n] >= 1).collect();
        let n1 = roots[rng.below(roots.len())];
        let mut t1 = Vec::new();
        d.flat_terms(n1, 1.0, &consumers, &mut t1);
        if t1.len() < 3 {
            return None;
        }
        let a = rng.below(t1.len());
        let mut b = rng.below(t1.len() - 1);
        if b >= a {
            b += 1;
        }
        let ((u, su), (v, sv)) = (t1[a], t1[b]);
        if u == v || t1.iter().filter(|&&(t, _)| t == u).count() != 1 || t1.iter().filter(|&&(t, _)| t == v).count() != 1 {
            return None;
        }
        // the other trees holding both, with the same relative sign
        let mut hosts: Vec<(usize, f64, Vec<(usize, f64)>)> = Vec::new();
        for &n2 in &roots {
            if n2 == n1 {
                continue;
            }
            let mut t2 = Vec::new();
            d.flat_terms(n2, 1.0, &consumers, &mut t2);
            if t2.len() < 3 || t2.iter().filter(|&&(t, _)| t == u).count() != 1 || t2.iter().filter(|&&(t, _)| t == v).count() != 1 {
                continue;
            }
            let (tu, tv) = (t2.iter().find(|&&(t, _)| t == u).unwrap().1, t2.iter().find(|&&(t, _)| t == v).unwrap().1);
            let s = if tu == su && tv == sv { 1.0 } else if tu == -su && tv == -sv { -1.0 } else { continue };
            hosts.push((n2, s, t2));
        }
        if hosts.is_empty() {
            return None;
        }
        let x = d.push(Node::Add { a: u, sa: su, b: v, sb: sv });
        let greedy = rng.unit() < 0.5;
        let mut rest: Vec<(usize, f64)> = t1.iter().cloned().filter(|&(t, _)| t != u && t != v).collect();
        rest.push((x, 1.0));
        d.redefine(n1, &rest, greedy, &quad, rng);
        for (n2, s, t2) in hosts {
            if reaches(&d, x, n2) {
                continue;
            }
            let mut rest: Vec<(usize, f64)> = t2.iter().cloned().filter(|&(t, _)| t != u && t != v).collect();
            rest.push((x, s));
            d.redefine(n2, &rest, greedy, &quad, rng);
        }
        return Some((4, d));
    }
    if r < 0.5 {
        // rebuild a sum tree, random or greedy
        let n = adds[rng.below(adds.len())];
        let mut terms = Vec::new();
        d.flat_terms(n, 1.0, &consumers, &mut terms);
        if terms.len() < 3 {
            return None;
        }
        let greedy = rng.unit() < 0.3;
        d.redefine(n, &terms, greedy, &quad, rng);
        Some((0, d))
    } else if r < 0.75 {
        // rotate: n = sx*x + sy*y with x = su*u + sv*v (x cloned if shared)
        let n = adds[rng.below(adds.len())];
        let (a, sa, b, sb) = match d.nodes[n] {
            Node::Add { a, sa, b, sb } => (a, sa, b, sb),
            _ => unreachable!(),
        };
        let (x, sx, y, sy) = if rng.unit() < 0.5 { (a, sa, b, sb) } else { (b, sb, a, sa) };
        let (u, su, v, sv) = match d.nodes[x] {
            Node::Add { a, sa, b, sb } => (a, sa, b, sb),
            _ => return None,
        };
        if x == n || u == n || v == n || y == x {
            return None;
        }
        // new grouping: n = (sx*su*u + sy*y) + sx*sv*v  or  n = (sx*sv*v + sy*y) + sx*su*u
        let (p, sp, q, sq) = if rng.unit() < 0.5 { (u, su, v, sv) } else { (v, sv, u, su) };
        let inner = d.push(Node::Add { a: p, sa: sx * sp, b: y, sb: sy });
        d.nodes[n] = Node::Add { a: inner, sa: 1.0, b: q, sb: sx * sq };
        Some((1, d))
    } else if r < 0.9 {
        // share: use an existing sum x = su*u + sv*v inside another tree that holds both u and v
        let x = adds[rng.below(adds.len())];
        let (u, su, v, sv) = match d.nodes[x] {
            Node::Add { a, sa, b, sb } => (a, sa, b, sb),
            _ => unreachable!(),
        };
        let n = adds[rng.below(adds.len())];
        if n == x {
            return None;
        }
        let mut terms = Vec::new();
        d.flat_terms(n, 1.0, &consumers, &mut terms);
        if terms.len() < 3 || terms.iter().any(|&(t, _)| t == x) {
            return None;
        }
        if u == v || terms.iter().filter(|&&(t, _)| t == u).count() != 1 || terms.iter().filter(|&&(t, _)| t == v).count() != 1 {
            return None;
        }
        let iu = terms.iter().position(|&(t, _)| t == u)?;
        let iv = terms.iter().position(|&(t, _)| t == v)?;
        let (tu, tv) = (terms[iu].1, terms[iv].1);
        // terms hold su'*u + sv'*v; this equals s*x iff (su', sv') = s*(su, sv)
        let s = if tu == su && tv == sv {
            1.0
        } else if tu == -su && tv == -sv {
            -1.0
        } else {
            return None;
        };
        let mut rest: Vec<(usize, f64)> = terms.iter().cloned().filter(|&(t, _)| t != u && t != v).collect();
        rest.push((x, s));
        // x must not depend on n (it would make a cycle): x is an existing node not under n
        if reaches(&d, x, n) {
            return None;
        }
        let greedy = rng.unit() < 0.5;
        d.redefine(n, &rest, greedy, &quad, rng);
        Some((2, d))
    } else {
        // unshare: clone a shared sum for one of its consumers
        let shared: Vec<usize> = adds.iter().cloned().filter(|&n| consumers[n] > 1).collect();
        if shared.is_empty() {
            return None;
        }
        let x = shared[rng.below(shared.len())];
        let clone = d.push(d.nodes[x].clone());
        // pick one consumer and point it at the clone
        let mut users: Vec<usize> = Vec::new();
        for n in 0..d.nodes.len() {
            match d.nodes[n] {
                Node::Add { a, b, .. } if a == x || b == x => users.push(n),
                Node::Scale { a, .. } if a == x => users.push(n),
                _ => {}
            }
        }
        if users.is_empty() {
            return None;
        }
        let n = users[rng.below(users.len())];
        match &mut d.nodes[n] {
            Node::Add { a, b, .. } => {
                if *a == x {
                    *a = clone;
                } else {
                    *b = clone;
                }
            }
            Node::Scale { a, .. } => *a = clone,
            _ => {}
        }
        Some((3, d))
    }
}

/// Does node `from` reach node `to` through its operands?
fn reaches(d: &Dag, from: usize, to: usize) -> bool {
    let mut stack = vec![from];
    let mut seen = vec![false; d.nodes.len()];
    while let Some(v) = stack.pop() {
        if v == to {
            return true;
        }
        if seen[v] {
            continue;
        }
        seen[v] = true;
        match d.nodes[v] {
            Node::In(_) => {}
            Node::Add { a, b, .. } => {
                stack.push(a);
                stack.push(b);
            }
            Node::Scale { a, .. } => stack.push(a),
        }
    }
    false
}

/// Simulated annealing from a start; returns the best DAG, its (objective, worst) and the
/// move statistics (proposed, accepted, improved the best) per move kind
fn anneal(start: &Dag, fixed: &Fixed, rows: &[Vec<f64>], check: bool, steps: usize, seed: u64, t0: f64, t1: f64) -> (Dag, (f64, f64), [[usize; 3]; 5]) {
    let mut rng = Rng::new(seed);
    let mut cur = start.clone();
    cur.compact();
    let mut cur_f = objective(fixed, &cur);
    let mut best = cur.clone();
    let mut best_f = cur_f;
    let mut stats = [[0usize; 3]; 5];
    for step in 0..steps {
        let t = t0 * (t1 / t0).powf(step as f64 / steps.max(1) as f64);
        let Some((kind, cand)) = propose(&cur, fixed, &mut rng) else { continue };
        stats[kind][0] += 1;
        let f = objective(fixed, &cand);
        if f.0 <= cur_f.0 || rng.unit() < ((cur_f.0 - f.0) / t).exp() {
            if check {
                if let Err(e) = check_forms(&cand, rows) {
                    panic!("move {} broke the program: {e}", MOVES[kind]);
                }
            }
            stats[kind][1] += 1;
            cur = cand;
            cur_f = f;
            if cur.nodes.len() > 4 * start.nodes.len() + 256 {
                cur.compact();
            }
            if f.0 < best_f.0 {
                stats[kind][2] += 1;
                best = cur.clone();
                best_f = f;
            }
        }
    }
    best.compact();
    (best, best_f, stats)
}

// ------------------------------------------------------------------ construction by model-scored CSE

/// A program under construction: every output is a flat list of (node, sign) terms over the
/// inputs and the subexpressions created so far; the completion sums each list greedily.
#[derive(Clone)]
struct Build {
    dag: Dag,                      // inputs, scaling leaves and the created subexpressions
    terms: Vec<Vec<(usize, f64)>>, // per output
}

impl Build {
    fn new(nin: usize, rows: &[Vec<f64>]) -> Build {
        let mut dag = Dag { nin, nodes: (0..nin).map(Node::In).collect(), outs: Vec::new() };
        let mut terms = Vec::new();
        for row in rows {
            let mut t = Vec::new();
            for (k, &c) in row.iter().enumerate() {
                if c != 0.0 {
                    t.push(dag.signed(k, c));
                }
            }
            terms.push(t);
        }
        Build { dag, terms }
    }

    /// The complete DAG: every output's terms summed greedily (smallest sums first)
    fn complete(&self, quad: &dyn Fn(&[f64]) -> f64) -> Dag {
        let mut d = self.dag.clone();
        d.outs.clear();
        for t in &self.terms {
            let (node, coef) = d.build_greedy(t, quad);
            d.outs.push((node, coef));
        }
        d
    }

    /// Candidate subexpressions: pairs of terms (a, b) with a relative sign that occur in two
    /// or more outputs; returns (a, sa, b, sb, outputs holding it with their sign)
    fn candidates(&self) -> Vec<(usize, f64, usize, f64, Vec<(usize, f64)>)> {
        let mut map: HashMap<(usize, usize, i8), Vec<(usize, f64)>> = HashMap::new();
        for (j, t) in self.terms.iter().enumerate() {
            for x in 0..t.len() {
                for y in x + 1..t.len() {
                    let ((a, sa), (b, sb)) = (t[x], t[y]);
                    if a == b {
                        continue;
                    }
                    // canonical: smaller node first, its sign taken as +1
                    let (a, sa, b, sb) = if a < b { (a, sa, b, sb) } else { (b, sb, a, sa) };
                    let rel = if sa * sb > 0.0 { 1i8 } else { -1i8 };
                    map.entry((a, b, rel)).or_default().push((j, sa));
                }
            }
        }
        map.into_iter()
            .filter(|(_, v)| v.len() >= 2 && v.iter().map(|x| x.0).collect::<std::collections::HashSet<_>>().len() == v.len())
            .map(|((a, b, rel), v)| (a, 1.0, b, rel as f64, v))
            .collect()
    }

    /// Apply a subexpression x = a + rel*b to the outputs holding it
    fn apply(&mut self, a: usize, b: usize, rel: f64, hosts: &[(usize, f64)]) {
        let x = self.dag.push(Node::Add { a, sa: 1.0, b, sb: rel });
        for &(j, s) in hosts {
            let t = &mut self.terms[j];
            let ia = t.iter().position(|&(n, _)| n == a).unwrap();
            t.remove(ia);
            let ib = t.iter().position(|&(n, _)| n == b).unwrap();
            t.remove(ib);
            t.push((x, s));
        }
    }
}

/// Greedy construction scored by the model: at each step the candidate subexpression whose
/// completion has the lowest objective is applied (softmax-random with temperature temp);
/// stops when no candidate improves.  Returns the best complete DAG and its objective.
fn construct(fixed: &Fixed, rows: &[Vec<f64>], nin: usize, temp: f64, seed: u64) -> (Dag, (f64, f64)) {
    let quad = |v: &[f64]| -> f64 {
        match fixed.which {
            Which::P => fixed.sch.quad(v),
            _ => v.iter().map(|x| x * x).sum(),
        }
    };
    let mut rng = Rng::new(seed);
    let mut b = Build::new(nin, rows);
    let mut cur = b.complete(&quad);
    let mut cur_f = objective(fixed, &cur);
    loop {
        let cands = b.candidates();
        if cands.is_empty() {
            break;
        }
        let mut scored: Vec<(f64, f64, usize)> = cands
            .par_iter()
            .enumerate()
            .map(|(k, (a, _, bb, rel, hosts))| {
                let mut trial = b.clone();
                trial.apply(*a, *bb, *rel, hosts);
                let f = objective(fixed, &trial.complete(&quad));
                (f.0, f.1, k)
            })
            .collect();
        scored.sort_by(|x, y| x.0.partial_cmp(&y.0).unwrap());
        let best = scored[0].0;
        if best >= cur_f.0 - 1e-12 {
            break;
        }
        // softmax over the improving candidates
        let improving: Vec<&(f64, f64, usize)> = scored.iter().filter(|s| s.0 < cur_f.0).collect();
        let chosen = if temp <= 0.0 || improving.len() == 1 {
            improving[0]
        } else {
            let weights: Vec<f64> = improving.iter().map(|s| (-(s.0 - best) / (temp * cur_f.0.max(1e-9))).exp()).collect();
            let total: f64 = weights.iter().sum();
            let mut u = rng.unit() * total;
            let mut pick = improving.len() - 1;
            for (i, w) in weights.iter().enumerate() {
                if u < *w {
                    pick = i;
                    break;
                }
                u -= w;
            }
            improving[pick]
        };
        let (a, _, bb, rel, hosts) = &cands[chosen.2];
        b.apply(*a, *bb, *rel, hosts);
        cur = b.complete(&quad);
        cur_f = objective(fixed, &cur);
    }
    cur.compact();
    (cur, cur_f)
}

fn arg(args: &[String], key: &str) -> Option<String> {
    args.iter().position(|a| a == key).map(|i| args[i + 1].clone())
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        eprintln!("usage: slpopt model|dagmodel NAME PREFIX [...] | slpopt search --scheme PREFIX --matrix L|R|P --out FILE [--init FILE] [--fixed PREFIX] [--steps N] [--restarts R] [--seed S] [--threads T]");
        std::process::exit(2);
    }
    match args[1].as_str() {
        "model" => {
            print_table_head();
            for pair in args[2..].chunks(2) {
                print_row(&pair[0], &analyse(&pair[1]));
            }
        }
        "dagmodel" => {
            // the same table, the three programs read as DAGs: validates the DAG model
            print_table_head();
            for pair in args[2..].chunks(2) {
                let prefix = &pair[1];
                let a = analyse(prefix);
                let sch = Scheme::new(
                    Program::parse(&format!("{prefix}_L.slp"), 16).pass(48).c,
                    Program::parse(&format!("{prefix}_R.slp"), 16).pass(48).c,
                    Program::parse(&format!("{prefix}_P.slp"), 48).pass(16).c,
                );
                let dl = Dag::parse(&format!("{prefix}_L.slp"), 16);
                let dr = Dag::parse(&format!("{prefix}_R.slp"), 16);
                let dp = Dag::parse(&format!("{prefix}_P.slp"), 48);
                let (lr_l, _, _) = dag_pass(&sch, Which::L, &dl);
                let (lr_r, _, _) = dag_pass(&sch, Which::R, &dr);
                let (pe, count, size) = dag_pass(&sch, Which::P, &dp);
                let b = summarize(&sch, lr_l, lr_r, pe, count, size, a.chain, a.roundings);
                print_row(&pair[0], &b);
            }
        }
        "score" => {
            // score programs of one matrix with the other two fixed: slpopt score --scheme PREFIX
            // --matrix M [--fixed PREFIX] FILE...
            let scheme = arg(&args, "--scheme").expect("--scheme PREFIX");
            let which = match arg(&args, "--matrix").expect("--matrix L|R|P").as_str() {
                "L" => Which::L,
                "R" => Which::R,
                "P" => Which::P,
                m => panic!("matrix {m}"),
            };
            let fixed_prefix = arg(&args, "--fixed").unwrap_or_else(|| scheme.clone());
            let sch = Scheme::from_sms(&scheme);
            let base = analyse(&fixed_prefix);
            let other: Vec<f64> = (0..16)
                .map(|j| match which {
                    Which::L => base.lr_r[j] + base.pe[j],
                    Which::R => base.lr_l[j] + base.pe[j],
                    Which::P => base.lr_l[j] + base.lr_r[j],
                })
                .collect();
            let fixed = Fixed { which, sch, other };
            let (nin, rows) = match which {
                Which::L => (16, fixed.sch.l.clone()),
                Which::R => (16, fixed.sch.r.clone()),
                Which::P => (48, fixed.sch.p.clone()),
            };
            let files: Vec<&String> = args[2..].iter().filter(|a| a.ends_with(".slp")).collect();
            for f in files {
                let dag = Dag::parse(f, nin);
                let ok = check_forms(&dag, &rows).is_ok();
                let (soft, worst) = objective(&fixed, &dag);
                let (part, _, _) = dag_pass(&fixed.sch, fixed.which, &dag);
                println!("{f} worst {worst:.4} soft {soft:.4} pass {:.4} nodes {} {}", mean(&part.iter().map(|&v| rel(v)).collect::<Vec<_>>()), dag.nodes.len(), if ok { "ok" } else { "WRONG" });
            }
        }
        "construct" => {
            // slpopt construct --scheme PREFIX --matrix M --out FILE [--fixed PREFIX] [--restarts R]
            //                  [--temp T] [--seed S]: greedy model-scored CSE construction
            let scheme = arg(&args, "--scheme").expect("--scheme PREFIX");
            let which = match arg(&args, "--matrix").expect("--matrix L|R|P").as_str() {
                "L" => Which::L,
                "R" => Which::R,
                "P" => Which::P,
                m => panic!("matrix {m}"),
            };
            let out = arg(&args, "--out").expect("--out FILE");
            let fixed_prefix = arg(&args, "--fixed").unwrap_or_else(|| scheme.clone());
            let restarts: usize = arg(&args, "--restarts").map(|s| s.parse().unwrap()).unwrap_or(4);
            let temp: f64 = arg(&args, "--temp").map(|s| s.parse().unwrap()).unwrap_or(0.0);
            let seed: u64 = arg(&args, "--seed").map(|s| s.parse().unwrap()).unwrap_or(1);
            let sch = Scheme::from_sms(&scheme);
            let base = analyse(&fixed_prefix);
            let other: Vec<f64> = (0..16)
                .map(|j| match which {
                    Which::L => base.lr_r[j] + base.pe[j],
                    Which::R => base.lr_l[j] + base.pe[j],
                    Which::P => base.lr_l[j] + base.lr_r[j],
                })
                .collect();
            let fixed = Fixed { which, sch, other };
            let (nin, rows) = match which {
                Which::L => (16, fixed.sch.l.clone()),
                Which::R => (16, fixed.sch.r.clone()),
                Which::P => (48, fixed.sch.p.clone()),
            };
            let mut best: Option<(Dag, (f64, f64))> = None;
            for k in 0..restarts {
                let (d, f) = construct(&fixed, &rows, nin, if k == 0 { 0.0 } else { temp }, seed + k as u64);
                if let Err(e) = check_forms(&d, &rows) {
                    panic!("construction does not compute the matrix: {e}");
                }
                eprintln!("# construct {k}: worst {:.4} (objective {:.4}), {} nodes", f.1, f.0, d.nodes.len());
                if best.as_ref().map_or(true, |b| f.0 < b.1 .0) {
                    best = Some((d, f));
                }
            }
            let (d, f) = best.unwrap();
            eprintln!("# best: worst {:.4} (objective {:.4})", f.1, f.0);
            std::fs::write(&out, d.to_slp()).unwrap();
        }
        "search" => {
            let scheme = arg(&args, "--scheme").expect("--scheme PREFIX");
            let which = match arg(&args, "--matrix").expect("--matrix L|R|P").as_str() {
                "L" => Which::L,
                "R" => Which::R,
                "P" => Which::P,
                m => panic!("matrix {m}"),
            };
            let out = arg(&args, "--out").expect("--out FILE");
            let fixed_prefix = arg(&args, "--fixed").unwrap_or_else(|| scheme.clone());
            let steps: usize = arg(&args, "--steps").map(|s| s.parse().unwrap()).unwrap_or(20000);
            let restarts: usize = arg(&args, "--restarts").map(|s| s.parse().unwrap()).unwrap_or(8);
            let seed: u64 = arg(&args, "--seed").map(|s| s.parse().unwrap()).unwrap_or(1);
            if let Some(t) = arg(&args, "--threads") {
                rayon::ThreadPoolBuilder::new().num_threads(t.parse().unwrap()).build_global().unwrap();
            }
            let sch = Scheme::from_sms(&scheme);
            // the other two passes' errors, from their fixed programs
            let base = analyse(&fixed_prefix);
            let other: Vec<f64> = (0..16)
                .map(|j| match which {
                    Which::L => base.lr_r[j] + base.pe[j],
                    Which::R => base.lr_l[j] + base.pe[j],
                    Which::P => base.lr_l[j] + base.lr_r[j],
                })
                .collect();
            let fixed = Fixed { which, sch, other };
            let (nin, rows) = match which {
                Which::L => (16, fixed.sch.l.clone()),
                Which::R => (16, fixed.sch.r.clone()),
                Which::P => (48, fixed.sch.p.clone()),
            };
            let start = match arg(&args, "--init") {
                Some(f) => Dag::parse(&f, nin),
                None => {
                    let quad = |v: &[f64]| -> f64 {
                        match which {
                            Which::P => fixed.sch.quad(v),
                            _ => v.iter().map(|x| x * x).sum(),
                        }
                    };
                    Dag::direct(nin, &rows, &quad)
                }
            };
            let check = args.iter().any(|a| a == "--check");
            if let Err(e) = check_forms(&start, &rows) {
                panic!("the start does not compute the matrix: {e}");
            }
            let (f0, w0) = objective(&fixed, &start);
            eprintln!("# start: worst {w0:.4} (objective {f0:.4}); fixed passes' worst {:.4}; {} nodes", fixed.other.iter().cloned().map(rel).fold(0.0, f64::max), start.nodes.len());
            let t0 = 0.02 * w0;
            let t1 = 0.0002 * w0;
            let results: Vec<(Dag, (f64, f64), [[usize; 3]; 5])> = (0..restarts)
                .into_par_iter()
                .map(|k| anneal(&start, &fixed, &rows, check, steps, seed.wrapping_mul(1000).wrapping_add(k as u64), t0, t1))
                .collect();
            for (k, (_, (f, w), st)) in results.iter().enumerate() {
                let s: Vec<String> = MOVES.iter().zip(st).map(|(m, c)| format!("{m} {}/{}/{}", c[0], c[1], c[2])).collect();
                eprintln!("# restart {k}: worst {w:.4} (objective {f:.4}); proposed/accepted/improved: {}", s.join(", "));
            }
            let (best, (fb, wb), _) = results.into_iter().min_by(|a, b| a.1 .0.partial_cmp(&b.1 .0).unwrap()).unwrap();
            if let Err(e) = check_forms(&best, &rows) {
                panic!("the result does not compute the matrix: {e}");
            }
            eprintln!("# best: worst {wb:.4} (objective {fb:.4}), {} nodes", best.nodes.len());
            std::fs::write(&out, best.to_slp()).unwrap();
            // check the written program reads back to the same error
            let back = Dag::parse(&out, nin);
            let (_, wback) = objective(&fixed, &back);
            eprintln!("# written {out}: worst {wback:.4} on re-reading");
        }
        other => {
            eprintln!("unknown command {other}");
            std::process::exit(2);
        }
    }
}
