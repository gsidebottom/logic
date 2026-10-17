//! xor47 — XOR-count minimization for F_2 linear maps with 16 inputs
//! (the legs of <4x4x4:r> mod-2 schemes).
//!
//! Core: randomized Boyar–Peralta.  A base S of signals starts as the 16
//! unit vectors; dist(t) = (min #signals of S summing to t) − 1 comes
//! exactly from a 2^16 table k[] updated in one pass per new signal
//! (k'(v) = min(k(v), 1 + k(v ^ s))).  Each step adds a target at
//! distance 1 if there is one, else the pair sum s_i ^ s_j that minimizes
//! the total distance (ties: max sum of squared distances, then random;
//! with probability --p the choice widens to totals within --slack of
//! the best).  Unused signals are removed afterwards.
//!
//! The product side P (16 x r) is optimized through its transpose
//! (r targets over 16 inputs) and emitted by Tellegen transposition, so
//! XOR(P) = XOR(P^T) + r − 16.  Programs are written in PLinOpt syntax;
//! matmul/x47/x47check.py is the independent referee.
//!
//! Usage:
//!   xor47 bp M.sms [--transpose] [--runs N] [--threads T] [--seed S]
//!            [--slack K] [--p P] [--pilot W] [--out M.slp]
//!     --pilot W: pilot method -- at each step try the top W candidates,
//!     complete each greedily, commit to the shortest completion
//!   xor47 scheme PREFIX [--out OUTPREFIX] [--runs N] [--threads T]
//!            [--seed S] [--slack K] [--p P]
//!     (reads PREFIX_{L,R,P}.sms, writes OUTPREFIX_{L,R,P}.slp)
use rayon::prelude::*;
use std::collections::HashMap;

const NIN: usize = 16;
const NV: usize = 1 << NIN;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
}

#[derive(Clone, Copy)]
struct Params {
    slack: u32,
    p: f64,
    pilot: usize,
}

/// A straight-line program over F_2^16: signal i < 16 is input i; signal
/// 16 + j is ops[j].0 ^ ops[j].1 (indices of earlier signals).
#[derive(Clone)]
struct Prog {
    val: Vec<u16>,
    ops: Vec<(usize, usize)>,
}

impl Prog {
    fn xors(&self) -> usize {
        self.ops.len()
    }
}

/// Search state: the program so far, the exact distance table
/// k[v] = min #signals summing to v, and a membership bitset.
#[derive(Clone)]
struct St {
    val: Vec<u16>,
    ops: Vec<(usize, usize)>,
    k: Vec<u8>,
    inb: Vec<u64>,
}

impl St {
    fn new() -> St {
        let k = (0..NV).map(|v| (v as u16).count_ones() as u8).collect();
        let mut st = St { val: Vec::with_capacity(96), ops: Vec::with_capacity(80), k, inb: vec![0; NV / 64] };
        for i in 0..NIN {
            st.val.push(1 << i);
            st.mark(1 << i);
        }
        st
    }
    fn has(&self, v: u16) -> bool {
        (self.inb[v as usize >> 6] >> (v & 63)) & 1 == 1
    }
    fn mark(&mut self, v: u16) {
        self.inb[v as usize >> 6] |= 1 << (v & 63);
    }
    /// add signal c (must be a sum of two current signals)
    fn add(&mut self, c: u16, rng: &mut Rng) {
        let n = self.val.len();
        let start = rng.below(n);
        let mut found = None;
        for off in 0..n {
            let i = (start + off) % n;
            let o = c ^ self.val[i];
            if o != self.val[i] && self.has(o) {
                let j = self.val.iter().position(|&x| x == o).unwrap();
                found = Some((i.min(j), i.max(j)));
                break;
            }
        }
        let (a, b) = found.expect("candidate must be a pair sum");
        self.ops.push((a, b));
        self.val.push(c);
        self.mark(c);
        let cu = c as usize;
        for v in 0..NV {
            let w = self.k[v ^ cu] + 1;
            if w < self.k[v] {
                self.k[v] = w;
            }
        }
    }
    fn rem(&self, targets: &[u16]) -> Vec<u16> {
        let mut r: Vec<u16> = targets.iter().copied().filter(|&t| t != 0 && self.k[t as usize] > 1).collect();
        r.sort_unstable();
        r.dedup();
        r
    }
    /// score every new pair sum: (total distance, sum of squares, value);
    /// returns the best total
    fn cands(&self, rem: &[u16], pool: &mut Vec<(u32, u32, u16)>, seen: &mut std::collections::HashSet<u16>) -> u32 {
        pool.clear();
        seen.clear();
        let n = self.val.len();
        let mut best = u32::MAX;
        for i in 0..n {
            let a = self.val[i];
            for j in (i + 1)..n {
                let c = a ^ self.val[j];
                if self.has(c) || !seen.insert(c) {
                    continue;
                }
                let (mut s, mut q) = (0u32, 0u32);
                for &t in rem {
                    let d = (self.k[t as usize] as u32 - 1).min(self.k[(t ^ c) as usize] as u32);
                    s += d;
                    q += d * d;
                }
                best = best.min(s);
                pool.push((s, q, c));
            }
        }
        best
    }
    fn prog(&self) -> Prog {
        Prog { val: self.val.clone(), ops: self.ops.clone() }
    }
}

/// Boyar–Peralta pick among scored candidates: totals within the slack
/// limit, max sum of squares, random among equals.
fn bp_pick(pool: &[(u32, u32, u16)], best: u32, rng: &mut Rng, prm: Params) -> u16 {
    let lim = if prm.slack > 0 && rng.unit() < prm.p { best + prm.slack } else { best };
    let (mut bq, mut cnt, mut pick) = (0u32, 0usize, 0u16);
    for &(s, q, c) in pool {
        if s > lim {
            continue;
        }
        if q > bq || cnt == 0 {
            bq = q;
            cnt = 1;
            pick = c;
        } else if q == bq {
            cnt += 1;
            if rng.below(cnt) == 0 {
                pick = c;
            }
        }
    }
    pick
}

/// distance-1 targets first (they cost one XOR whenever they are made)
fn dist1(st: &St, rem: &[u16], rng: &mut Rng) -> Option<u16> {
    let d1: Vec<u16> = rem.iter().copied().filter(|&t| st.k[t as usize] == 2).collect();
    if d1.is_empty() { None } else { Some(d1[rng.below(d1.len())]) }
}

/// greedy Boyar–Peralta from the current state to completion
fn bp_complete(st: &mut St, targets: &[u16], rng: &mut Rng, prm: Params) {
    let mut pool = Vec::with_capacity(4096);
    let mut seen = std::collections::HashSet::new();
    loop {
        let rem = st.rem(targets);
        if rem.is_empty() {
            break;
        }
        let c = match dist1(st, &rem, rng) {
            Some(c) => c,
            None => {
                let best = st.cands(&rem, &mut pool, &mut seen);
                bp_pick(&pool, best, rng, prm)
            }
        };
        st.add(c, rng);
    }
}

/// Pilot method: at each step, complete greedily after each of the top
/// `width` candidates and commit to the one with the shortest completion.
fn pilot_run(targets: &[u16], rng: &mut Rng, prm: Params) -> Prog {
    let mut st = St::new();
    let mut best: Option<Prog> = None;
    let mut pool = Vec::with_capacity(4096);
    let mut seen = std::collections::HashSet::new();
    let greedy = Params { slack: 0, p: 0.0, pilot: 0 };
    loop {
        let rem = st.rem(targets);
        if rem.is_empty() {
            break;
        }
        let c = match dist1(&st, &rem, rng) {
            Some(c) => c,
            None => {
                st.cands(&rem, &mut pool, &mut seen);
                for i in (1..pool.len()).rev() {
                    let j = rng.below(i + 1);
                    pool.swap(i, j);
                }
                pool.sort_by(|a, b| a.0.cmp(&b.0).then(b.1.cmp(&a.1)));
                let mut pick = (usize::MAX, 0u16);
                for &(_, _, c) in pool.iter().take(prm.pilot) {
                    let mut s2 = st.clone();
                    s2.add(c, rng);
                    bp_complete(&mut s2, targets, rng, greedy);
                    let p = dce(&s2.prog(), targets);
                    if p.xors() < pick.0 {
                        pick = (p.xors(), c);
                    }
                    if best.as_ref().map_or(true, |b| p.xors() < b.xors()) {
                        best = Some(p);
                    }
                }
                pick.1
            }
        };
        st.add(c, rng);
    }
    let p = dce(&st.prog(), targets);
    match best {
        Some(b) if b.xors() < p.xors() => b,
        _ => p,
    }
}

fn bp_run(targets: &[u16], rng: &mut Rng, prm: Params) -> Prog {
    if prm.pilot > 0 {
        return pilot_run(targets, rng, prm);
    }
    let mut st = St::new();
    bp_complete(&mut st, targets, rng, prm);
    st.prog()
}

/// Remove signals that no target depends on; renumber.
fn dce(prog: &Prog, targets: &[u16]) -> Prog {
    let n = prog.val.len();
    let mut need = vec![false; n];
    let want: std::collections::HashSet<u16> = targets.iter().copied().collect();
    for s in NIN..n {
        if want.contains(&prog.val[s]) {
            need[s] = true;
        }
    }
    for s in (NIN..n).rev() {
        if need[s] {
            let (a, b) = prog.ops[s - NIN];
            need[a] = true;
            need[b] = true;
        }
    }
    let mut map = vec![usize::MAX; n];
    let mut out = Prog { val: Vec::new(), ops: Vec::new() };
    for i in 0..NIN {
        map[i] = i;
        out.val.push(prog.val[i]);
    }
    for s in NIN..n {
        if need[s] {
            let (a, b) = prog.ops[s - NIN];
            map[s] = out.val.len();
            out.ops.push((map[a], map[b]));
            out.val.push(prog.val[s]);
        }
    }
    out
}

fn verify(prog: &Prog, targets: &[u16]) {
    for (j, &(a, b)) in prog.ops.iter().enumerate() {
        assert_eq!(prog.val[NIN + j], prog.val[a] ^ prog.val[b], "bad op");
        assert!(a < NIN + j && b < NIN + j, "op uses a later signal");
    }
    let have: std::collections::HashSet<u16> = prog.val.iter().copied().collect();
    for &t in targets {
        assert!(t == 0 || have.contains(&t), "target {t:#06x} missing");
    }
}

fn optimize(targets: &[u16], runs: usize, seed: u64, prm: Params) -> (Prog, Vec<usize>) {
    let results: Vec<Prog> = (0..runs)
        .into_par_iter()
        .map(|r| {
            let mut rng = Rng(seed ^ (r as u64).wrapping_mul(0xA24B_AED4_963E_E407));
            let p = bp_run(targets, &mut rng, prm);
            dce(&p, targets)
        })
        .collect();
    let mut hist = vec![0usize; 200];
    for p in &results {
        hist[p.xors().min(199)] += 1;
    }
    let best = results.into_iter().min_by_key(|p| p.xors()).unwrap();
    verify(&best, targets);
    (best, hist)
}

// ---------------------------------------------------------------- I/O

/// rows x cols matrix mod 2 as row bitmasks (u64; cols <= 64)
fn read_sms(path: &str) -> (usize, usize, Vec<u64>) {
    let txt = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut it = txt.lines();
    let hdr: Vec<usize> = it.next().unwrap().split_whitespace().take(2).map(|s| s.parse().unwrap()).collect();
    let (rows, cols) = (hdr[0], hdr[1]);
    assert!(cols <= 64 && rows <= 64);
    let mut m = vec![0u64; rows];
    for ln in it {
        let f: Vec<&str> = ln.split_whitespace().collect();
        if f.len() < 3 {
            continue;
        }
        let (i, j): (usize, usize) = (f[0].parse().unwrap(), f[1].parse().unwrap());
        if i == 0 && j == 0 {
            break;
        }
        let v: i64 = f[2].parse().unwrap_or_else(|_| panic!("{path}: non-integer entry {ln}"));
        if v.rem_euclid(2) == 1 {
            m[i - 1] ^= 1u64 << (j - 1);
        }
    }
    (rows, cols, m)
}

fn transpose(rows: usize, cols: usize, m: &[u64]) -> Vec<u64> {
    (0..cols)
        .map(|c| (0..rows).fold(0u64, |acc, r| acc | (((m[r] >> c) & 1) << r)))
        .collect()
}

fn sig_name(s: usize, tmp: &str) -> String {
    if s < NIN {
        format!("i{s}")
    } else {
        format!("{tmp}{}", s - NIN)
    }
}

/// Program for M (rows over 16 inputs): outputs o<row>.
fn emit_direct(prog: &Prog, rows: &[u16]) -> (String, usize) {
    let mut out = String::new();
    let mut xors = 0;
    let mut first_row: HashMap<u16, usize> = HashMap::new();
    for (r, &v) in rows.iter().enumerate() {
        first_row.entry(v).or_insert(r);
    }
    let mut name: Vec<String> = (0..prog.val.len()).map(|s| sig_name(s, "t")).collect();
    for (j, &(a, b)) in prog.ops.iter().enumerate() {
        let s = NIN + j;
        if let Some(&r) = first_row.get(&prog.val[s]) {
            name[s] = format!("o{r}");
        }
        out += &format!("{}:={}+{};\n", name[s], name[a], name[b]);
        xors += 1;
    }
    let idx: HashMap<u16, usize> = prog.val.iter().enumerate().map(|(s, &v)| (v, s)).collect();
    for (r, &v) in rows.iter().enumerate() {
        if v == 0 {
            continue;
        }
        let s = idx[&v];
        let want = format!("o{r}");
        if name[s] != want {
            out += &format!("{want}:={};\n", name[s]);
        }
    }
    (out, xors)
}

/// Program for P (16 outputs over r inputs) from a program for P^T
/// (r targets over 16 inputs) by transposition.
fn emit_transposed(prog: &Prog, cols: &[u16]) -> (String, usize) {
    let n = prog.val.len();
    let idx: HashMap<u16, usize> = prog.val.iter().enumerate().map(|(s, &v)| (v, s)).collect();
    let mut adj: Vec<Vec<String>> = vec![Vec::new(); n];
    for (k, &v) in cols.iter().enumerate() {
        if v != 0 {
            adj[idx[&v]].push(format!("i{k}"));
        }
    }
    let mut out = String::new();
    let mut xors = 0;
    for s in (NIN..n).rev() {
        let terms = std::mem::take(&mut adj[s]);
        if terms.is_empty() {
            continue;
        }
        let nm = if terms.len() == 1 {
            terms[0].clone()
        } else {
            let nm = format!("y{}", s - NIN);
            out += &format!("{nm}:={};\n", terms.join("+"));
            xors += terms.len() - 1;
            nm
        };
        let (a, b) = prog.ops[s - NIN];
        adj[a].push(nm.clone());
        adj[b].push(nm);
    }
    for c in 0..NIN {
        let terms = &adj[c];
        assert!(!terms.is_empty(), "output o{c} depends on no product");
        out += &format!("o{c}:={};\n", terms.join("+"));
        xors += terms.len() - 1;
    }
    (out, xors)
}

struct Opts {
    runs: usize,
    threads: usize,
    seed: u64,
    prm: Params,
    out: Option<String>,
    transpose: bool,
}

fn parse_opts(args: &[String]) -> Opts {
    let mut o = Opts {
        runs: 2000,
        threads: 10,
        seed: 1,
        prm: Params { slack: 0, p: 0.0, pilot: 0 },
        out: None,
        transpose: false,
    };
    let mut i = 0;
    while i < args.len() {
        let a = args[i].as_str();
        let mut val = || {
            i += 1;
            args.get(i).cloned().unwrap_or_else(|| panic!("{a} needs a value"))
        };
        match a {
            "--runs" => o.runs = val().parse().unwrap(),
            "--threads" => o.threads = val().parse().unwrap(),
            "--seed" => o.seed = val().parse().unwrap(),
            "--slack" => o.prm.slack = val().parse().unwrap(),
            "--p" => o.prm.p = val().parse().unwrap(),
            "--pilot" => o.prm.pilot = val().parse().unwrap(),
            "--out" => o.out = Some(val()),
            "--transpose" => o.transpose = true,
            _ => panic!("unknown option {a}"),
        }
        i += 1;
    }
    o
}

fn hist_str(h: &[usize]) -> String {
    h.iter()
        .enumerate()
        .filter(|(_, c)| **c > 0)
        .take(8)
        .map(|(x, c)| format!("{x}:{c}"))
        .collect::<Vec<_>>()
        .join(" ")
}

/// Optimize one side; returns (program text, XOR count, histogram).
fn side(m: &[u64], rows: usize, cols: usize, transposed: bool, o: &Opts) -> (String, usize, String) {
    let targets: Vec<u16> = if transposed {
        assert_eq!(rows, NIN, "transposed side must have 16 rows");
        transpose(rows, cols, m).iter().map(|&v| v as u16).collect()
    } else {
        assert_eq!(cols, NIN, "direct side must have 16 columns");
        m.iter().map(|&v| v as u16).collect()
    };
    let (best, hist) = optimize(&targets, o.runs, o.seed, o.prm);
    let (txt, x) = if transposed { emit_transposed(&best, &targets) } else { emit_direct(&best, &targets) };
    let expect = if transposed {
        let nz = targets.iter().filter(|&&t| t != 0).count();
        best.xors() + nz - NIN
    } else {
        best.xors()
    };
    assert_eq!(x, expect, "emitted count disagrees with the program");
    (txt, x, hist_str(&hist))
}

// ------------------------------------------------- 4x4 algebra over F_2
// A 4x4 matrix is a u16, row-major: bit 4i+j holds entry (i, j) -- the
// same layout as an sms row over the 16 row-major entries of A, B or C.

fn m_mul(a: u16, b: u16) -> u16 {
    let mut out = 0u16;
    for i in 0..4 {
        let mut r = 0u16;
        for j in 0..4 {
            if (a >> (4 * i + j)) & 1 == 1 {
                r ^= (b >> (4 * j)) & 0xF;
            }
        }
        out |= r << (4 * i);
    }
    out
}

fn m_t(a: u16) -> u16 {
    let mut out = 0u16;
    for i in 0..4 {
        for j in 0..4 {
            if (a >> (4 * i + j)) & 1 == 1 {
                out |= 1 << (4 * j + i);
            }
        }
    }
    out
}

fn m_inv(a: u16) -> Option<u16> {
    let mut r: [u16; 4] = [0; 4];
    for (i, ri) in r.iter_mut().enumerate() {
        *ri = ((a >> (4 * i)) & 0xF) | (1 << (4 + i)); // [A | I]
    }
    for c in 0..4 {
        let p = (c..4).find(|&i| (r[i] >> c) & 1 == 1)?;
        r.swap(c, p);
        for i in 0..4 {
            if i != c && (r[i] >> c) & 1 == 1 {
                r[i] ^= r[c];
            }
        }
    }
    Some((0..4).fold(0u16, |acc, i| acc | (((r[i] >> 4) & 0xF) << (4 * i))))
}

/// all (X, X^-1) in GL(4,2)
fn gl42() -> Vec<(u16, u16)> {
    (0..=u16::MAX).filter_map(|a| m_inv(a).map(|b| (a, b))).collect()
}

/// A scheme: product k = <U_k, A> <V_k, B>, C = sum_k product_k W_k.
#[derive(Clone)]
struct Scheme {
    u: Vec<u16>,
    v: Vec<u16>,
    w: Vec<u16>,
}

impl Scheme {
    fn from_sms(pre: &str) -> Scheme {
        let (rl, cl, l) = read_sms(&format!("{pre}_L.sms"));
        let (rr, cr, r) = read_sms(&format!("{pre}_R.sms"));
        let (rp, cp, p) = read_sms(&format!("{pre}_P.sms"));
        assert!(cl == NIN && cr == NIN && rp == NIN && rl == rr && rr == cp, "bad scheme shapes");
        Scheme {
            u: l.iter().map(|&x| x as u16).collect(),
            v: r.iter().map(|&x| x as u16).collect(),
            w: transpose(rp, cp, &p).iter().map(|&x| x as u16).collect(),
        }
    }

    /// all 256 basis pairs: sum_k U_k[a] V_k[b] W_k == Vect(E_a E_b)
    fn brent_ok(&self) -> bool {
        for a in 0..NIN {
            for b in 0..NIN {
                let mut got = 0u16;
                for k in 0..self.u.len() {
                    if (self.u[k] >> a) & 1 == 1 && (self.v[k] >> b) & 1 == 1 {
                        got ^= self.w[k];
                    }
                }
                let (ai, aj, bi, bj) = (a / 4, a % 4, b / 4, b % 4);
                let want = if aj == bi { 1u16 << (4 * ai + bj) } else { 0 };
                if got != want {
                    return false;
                }
            }
        }
        true
    }

    /// slot symmetry sigma in 0..6 (cyclic shifts, then transposition)
    fn sym(&self, sigma: usize) -> Scheme {
        let t = |x: &Vec<u16>| x.iter().map(|&m| m_t(m)).collect::<Vec<u16>>();
        let (u, v, w) = (self.u.clone(), self.v.clone(), self.w.clone());
        let (u, v, w) = match sigma {
            0 => (u, v, w),
            1 => (v.clone(), t(&w), t(&u)),
            2 => (t(&w), u.clone(), t(&v)),
            3 => (t(&v), t(&u), t(&w)),
            4 => (w.clone(), t(&v), u.clone()),
            5 => (t(&u), w.clone(), v.clone()),
            _ => unreachable!(),
        };
        Scheme { u, v, w }
    }

    /// U' = X^T U Y^-T, V' = Y^T V Z^-T, W' = X^-1 W Z
    fn act(&self, x: (u16, u16), y: (u16, u16), z: (u16, u16)) -> Scheme {
        let (xt, yt, yit, zit) = (m_t(x.0), m_t(y.0), m_t(y.1), m_t(z.1));
        Scheme {
            u: self.u.iter().map(|&m| m_mul(m_mul(xt, m), yit)).collect(),
            v: self.v.iter().map(|&m| m_mul(m_mul(yt, m), zit)).collect(),
            w: self.w.iter().map(|&m| m_mul(m_mul(x.1, m), z.0)).collect(),
        }
    }

    fn write_sms(&self, pre: &str) {
        let r = self.u.len();
        let rows = |m: &[u16], path: String| {
            let mut s = format!("{} {} M\n", m.len(), NIN);
            for (i, &x) in m.iter().enumerate() {
                for j in 0..NIN {
                    if (x >> j) & 1 == 1 {
                        s += &format!("{} {} 1\n", i + 1, j + 1);
                    }
                }
            }
            s += "0 0 0\n";
            std::fs::write(path, s).unwrap();
        };
        rows(&self.u, format!("{pre}_L.sms"));
        rows(&self.v, format!("{pre}_R.sms"));
        let mut s = format!("{} {} M\n", NIN, r);
        for p in 0..NIN {
            for (k, &x) in self.w.iter().enumerate() {
                if (x >> p) & 1 == 1 {
                    s += &format!("{} {} 1\n", p + 1, k + 1);
                }
            }
        }
        s += "0 0 0\n";
        std::fs::write(format!("{pre}_P.sms"), s).unwrap();
    }
}

/// distinct non-unit targets (a lower bound on XORs) and total weight
fn proxy(m: &[u16], stamp: &mut [u32], tick: &mut u32) -> (u32, u32) {
    *tick += 1;
    let (mut lb, mut wt) = (0u32, 0u32);
    for &x in m {
        let c = x.count_ones();
        wt += c;
        if c > 1 && stamp[x as usize] != *tick {
            stamp[x as usize] = *tick;
            lb += 1;
        }
    }
    (lb, wt)
}

/// per-thread workspace for single BP runs inside the orbit search
struct Ws {
    stamp: Vec<u32>,
    tick: u32,
    rng: Rng,
}

impl Ws {
    fn new(seed: u64) -> Ws {
        Ws { stamp: vec![0; NV], tick: 0, rng: Rng(seed) }
    }
    fn bp(&mut self, t: &[u16], runs: usize, prm: Params) -> Prog {
        let mut best: Option<Prog> = None;
        for _ in 0..runs {
            let p = dce(&bp_run(t, &mut self.rng, prm), t);
            if best.as_ref().map_or(true, |b| p.xors() < b.xors()) {
                best = Some(p);
            }
        }
        best.unwrap()
    }
}

/// total XORs of a scheme: XOR(L) + XOR(R) + XOR(P^T) + (r - 16)
fn scheme_cost(s: &Scheme, ws: &mut Ws, runs: usize, prm: Params) -> (usize, [Prog; 3]) {
    let pl = ws.bp(&s.u, runs, prm);
    let pr = ws.bp(&s.v, runs, prm);
    let pp = ws.bp(&s.w, runs, prm);
    let nz = s.w.iter().filter(|&&x| x != 0).count();
    (pl.xors() + pr.xors() + pp.xors() + nz - NIN, [pl, pr, pp])
}

/// One coordinate step: choose the best of all 20160 values for slot c
/// (0 = X, 1 = Y, 2 = Z) given the other two; returns the new value.
fn coord_step(
    base: &Scheme,
    g: &[(u16, u16)],
    cur: [(u16, u16); 3],
    c: usize,
    topk: usize,
    ws: &mut Ws,
) -> ((u16, u16), usize) {
    let r = base.u.len();
    // sides touched: X -> (u, w), Y -> (u, v), Z -> (v, w)
    let mut cand: Vec<(u32, u32, usize)> = Vec::with_capacity(g.len());
    let mut a = vec![0u16; r];
    let mut b = vec![0u16; r];
    let (x, y, z) = (cur[0], cur[1], cur[2]);
    let pre: (Vec<u16>, Vec<u16>) = match c {
        0 => (
            base.u.iter().map(|&m| m_mul(m, m_t(y.1))).collect(),
            base.w.iter().map(|&m| m_mul(m, z.0)).collect(),
        ),
        1 => (
            base.u.iter().map(|&m| m_mul(m_t(x.0), m)).collect(),
            base.v.iter().map(|&m| m_mul(m, m_t(z.1))).collect(),
        ),
        _ => (
            base.v.iter().map(|&m| m_mul(m_t(y.0), m)).collect(),
            base.w.iter().map(|&m| m_mul(x.1, m)).collect(),
        ),
    };
    let fill = |gi: usize, a: &mut [u16], b: &mut [u16]| {
        let (gm, gi_) = g[gi];
        for k in 0..r {
            match c {
                0 => {
                    a[k] = m_mul(m_t(gm), pre.0[k]);
                    b[k] = m_mul(gi_, pre.1[k]);
                }
                1 => {
                    a[k] = m_mul(pre.0[k], m_t(gi_));
                    b[k] = m_mul(m_t(gm), pre.1[k]);
                }
                _ => {
                    a[k] = m_mul(pre.0[k], m_t(gi_));
                    b[k] = m_mul(pre.1[k], gm);
                }
            }
        }
    };
    for gi in 0..g.len() {
        fill(gi, &mut a, &mut b);
        let (la, wa) = proxy(&a, &mut ws.stamp, &mut ws.tick);
        let (lb, wb) = proxy(&b, &mut ws.stamp, &mut ws.tick);
        cand.push((la + lb, wa + wb, gi));
    }
    // random order among equal proxies, then the best topk by proxy
    for i in (1..cand.len()).rev() {
        let j = ws.rng.below(i + 1);
        cand.swap(i, j);
    }
    cand.sort_by_key(|&(l, w, _)| (l, w));
    let mut best = (usize::MAX, 0usize);
    let prm = Params { slack: 0, p: 0.0, pilot: 0 };
    for &(_, _, gi) in cand.iter().take(topk) {
        fill(gi, &mut a, &mut b);
        let s = ws.bp(&a, 1, prm).xors() + ws.bp(&b, 1, prm).xors();
        if s < best.0 {
            best = (s, gi);
        }
    }
    (g[best.1], best.0)
}

struct OrbitOpts {
    restarts: usize,
    sweeps: usize,
    topk: usize,
    final_runs: usize,
}

fn orbit(pre: &str, o: &Opts, oo: &OrbitOpts) {
    let s0 = Scheme::from_sms(pre);
    assert!(s0.brent_ok(), "input scheme fails Brent");
    let syms: Vec<Scheme> = (0..6).map(|i| s0.sym(i)).collect();
    for (i, s) in syms.iter().enumerate() {
        assert!(s.brent_ok(), "symmetry {i} breaks Brent");
    }
    let g = gl42();
    assert_eq!(g.len(), 20160);
    let id = (0x8421u16, 0x8421u16);
    // gate the action on the object: random elements must keep Brent
    {
        let mut rng = Rng(o.seed);
        for _ in 0..20 {
            let (x, y, z) = (g[rng.below(g.len())], g[rng.below(g.len())], g[rng.below(g.len())]);
            assert!(syms[rng.below(6)].act(x, y, z).brent_ok(), "GL action breaks Brent");
        }
    }
    let r = s0.u.len();
    let outdir = o.out.clone().unwrap_or_else(|| ".".into());
    std::fs::create_dir_all(&outdir).unwrap();
    let best = std::sync::Mutex::new(usize::MAX);
    let fprm = o.prm;
    (0..oo.restarts).into_par_iter().for_each(|rs| {
        let mut ws = Ws::new(o.seed ^ (rs as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let sigma = if rs == 0 { 0 } else { ws.rng.below(6) };
        let base = &syms[sigma];
        let mut cur = if rs == 0 {
            [id, id, id]
        } else {
            [g[ws.rng.below(g.len())], g[ws.rng.below(g.len())], g[ws.rng.below(g.len())]]
        };
        let (mut cost, _) = scheme_cost(&base.act(cur[0], cur[1], cur[2]), &mut ws, 1, Params { slack: 0, p: 0.0, pilot: 0 });
        for _ in 0..oo.sweeps {
            let before = cost;
            for c in 0..3 {
                let (gv, _) = coord_step(base, &g, cur, c, oo.topk, &mut ws);
                let mut trial = cur;
                trial[c] = gv;
                let (tc, _) = scheme_cost(&base.act(trial[0], trial[1], trial[2]), &mut ws, 1, Params { slack: 0, p: 0.0, pilot: 0 });
                if tc <= cost {
                    cur = trial;
                    cost = tc;
                }
            }
            if cost >= before {
                break;
            }
        }
        let s = base.act(cur[0], cur[1], cur[2]);
        let (fc, progs) = scheme_cost(&s, &mut ws, oo.final_runs, fprm);
        let mut b = best.lock().unwrap();
        let tag = if fc < *b { " NEW BEST" } else { "" };
        println!(
            "restart {rs}: sigma {sigma} X {:04x} Y {:04x} Z {:04x}  quick {cost} final {fc} (L {} R {} P {}){tag}",
            cur[0].0, cur[1].0, cur[2].0, progs[0].xors(), progs[1].xors(), progs[2].xors() + r - NIN
        );
        if fc < *b {
            *b = fc;
            assert!(s.brent_ok(), "orbit point fails Brent");
            let p = format!("{outdir}/orbit_{fc}");
            s.write_sms(&p);
            let (tl, _) = emit_direct(&progs[0], &s.u);
            let (tr, _) = emit_direct(&progs[1], &s.v);
            let (tp, _) = emit_transposed(&progs[2], &s.w);
            std::fs::write(format!("{p}_L.slp"), tl).unwrap();
            std::fs::write(format!("{p}_R.slp"), tr).unwrap();
            std::fs::write(format!("{p}_P.slp"), tp).unwrap();
        }
    });
    println!("best {}", best.lock().unwrap());
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 {
        eprintln!("usage: xor47 bp M.sms [opts] | xor47 scheme PREFIX [opts] | xor47 orbit PREFIX [opts]");
        std::process::exit(2);
    }
    if args[1] == "orbit" {
        // orbit-specific options are stripped before the shared parser
        let mut rest = Vec::new();
        let mut oo = OrbitOpts { restarts: 24, sweeps: 6, topk: 200, final_runs: 64 };
        let mut i = 3;
        while i < args.len() {
            match args[i].as_str() {
                "--restarts" => { oo.restarts = args[i + 1].parse().unwrap(); i += 2; }
                "--sweeps" => { oo.sweeps = args[i + 1].parse().unwrap(); i += 2; }
                "--topk" => { oo.topk = args[i + 1].parse().unwrap(); i += 2; }
                "--final-runs" => { oo.final_runs = args[i + 1].parse().unwrap(); i += 2; }
                _ => { rest.push(args[i].clone()); i += 1; }
            }
        }
        let o = parse_opts(&rest);
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
        let t0 = std::time::Instant::now();
        orbit(&args[2], &o, &oo);
        println!("({:.1}s)", t0.elapsed().as_secs_f64());
        return;
    }
    let o = parse_opts(&args[3..]);
    rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
    let t0 = std::time::Instant::now();
    match args[1].as_str() {
        "bp" => {
            let (rows, cols, m) = read_sms(&args[2]);
            let (txt, x, h) = side(&m, rows, cols, o.transpose, &o);
            println!("{}: {x} XORs  (runs {}, hist {h}, {:.1}s)", args[2], o.runs, t0.elapsed().as_secs_f64());
            if let Some(p) = &o.out {
                std::fs::write(p, txt).unwrap();
            }
        }
        "scheme" => {
            let pre = &args[2];
            let mut total = 0;
            for (s, tr) in [("L", false), ("R", false), ("P", true)] {
                let (rows, cols, m) = read_sms(&format!("{pre}_{s}.sms"));
                let (txt, x, h) = side(&m, rows, cols, tr, &o);
                println!("{s}: {x} XORs  (hist {h})");
                total += x;
                if let Some(p) = &o.out {
                    std::fs::write(format!("{p}_{s}.slp"), txt).unwrap();
                }
            }
            println!("total {total} XORs  (runs {} per side, {:.1}s)", o.runs, t0.elapsed().as_secs_f64());
        }
        c => panic!("unknown command {c}"),
    }
}
