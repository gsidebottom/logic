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
//!   xor47 orbit PREFIX [--restarts N] [--sweeps S] [--topk K]
//!            [--final-runs F] [--anneal STEPS --t0 T0 --t1 T1] [opts]
//!     symmetry-orbit search: coordinate descent over GL(4,2)^3 (each
//!     step scans all 20160 values of one coordinate, shortlists topk by
//!     a structural proxy, scores them by BP), or with --anneal,
//!     simulated annealing by elementary-matrix moves
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
    target: usize,
    cap: f64,
    depth: usize,
    maxsub: usize,
    runs: usize,
    threads: usize,
    seed: u64,
    prm: Params,
    out: Option<String>,
    transpose: bool,
    budget: f64,
    chunk: usize,
}

fn parse_opts(args: &[String]) -> Opts {
    let mut o = Opts {
        target: 0,
        cap: 30.0,
        depth: 3,
        maxsub: 200,
        runs: 2000,
        threads: 10,
        seed: 1,
        prm: Params { slack: 0, p: 0.0, pilot: 0 },
        out: None,
        transpose: false,
        budget: 0.0,
        chunk: 2000,
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
            "--depth" => o.depth = val().parse().unwrap(),
            "--cap" => o.cap = val().parse().unwrap(),
            "--target" => o.target = val().parse().unwrap(),
            "--maxsub" => o.maxsub = val().parse().unwrap(),
            "--budget" => o.budget = val().parse().unwrap(),
            "--chunk" => o.chunk = val().parse().unwrap(),
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
    anneal: usize,
    t0: f64,
    t1: f64,
    collect: usize,
}

/// side costs (BP, one run each) of the scheme at cur
fn side_costs(base: &Scheme, cur: [(u16, u16); 3], ws: &mut Ws) -> [usize; 3] {
    let s = base.act(cur[0], cur[1], cur[2]);
    let g = Params { slack: 0, p: 0.0, pilot: 0 };
    [ws.bp(&s.u, 1, g).xors(), ws.bp(&s.v, 1, g).xors(), ws.bp(&s.w, 1, g).xors()]
}

/// Simulated annealing over (X, Y, Z): a move multiplies one coordinate
/// by an elementary transvection I + E_ij on the left or the right and
/// re-scores the two sides it touches (X: L, P; Y: L, R; Z: R, P).
fn anneal_restart(
    base: &Scheme,
    mut cur: [(u16, u16); 3],
    oo: &OrbitOpts,
    ws: &mut Ws,
    keep: &mut Vec<([(u16, u16); 3], usize)>,
) -> ([(u16, u16); 3], usize) {
    let mut sc = side_costs(base, cur, ws);
    let mut cost: usize = sc.iter().sum();
    let mut best = (cur, cost);
    let mut seen = std::collections::HashSet::new();
    let touched = [[0usize, 2], [0, 1], [1, 2]];
    let g = Params { slack: 0, p: 0.0, pilot: 0 };
    for step in 0..oo.anneal {
        let temp = oo.t0 * (oo.t1 / oo.t0).powf(step as f64 / oo.anneal.max(1) as f64);
        let c = ws.rng.below(3);
        let (i, j) = loop {
            let (i, j) = (ws.rng.below(4), ws.rng.below(4));
            if i != j {
                break (i, j);
            }
        };
        let tv = 0x8421u16 | (1 << (4 * i + j)); // its own inverse over F_2
        let (gm, gi) = cur[c];
        let nv = if ws.rng.below(2) == 0 { (m_mul(tv, gm), m_mul(gi, tv)) } else { (m_mul(gm, tv), m_mul(tv, gi)) };
        let mut trial = cur;
        trial[c] = nv;
        let s = base.act(trial[0], trial[1], trial[2]);
        let mut nsc = sc;
        for &side in &touched[c] {
            let m = match side { 0 => &s.u, 1 => &s.v, _ => &s.w };
            nsc[side] = ws.bp(m, 1, g).xors();
        }
        let ncost: usize = nsc.iter().sum();
        let d = ncost as f64 - cost as f64;
        if d <= 0.0 || ws.rng.unit() < (-d / temp).exp() {
            cur = trial;
            sc = nsc;
            cost = ncost;
            if cost < best.1 {
                best = (cur, cost);
            }
            if oo.collect > 0 && cost + 31 <= oo.collect && seen.insert((cur[0].0, cur[1].0, cur[2].0)) {
                keep.push((cur, cost + 31));
            }
        }
    }
    best
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
    let cands_lock = std::sync::Mutex::new(());
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
        if oo.anneal > 0 {
            let mut keep = Vec::new();
            let (c2, q) = anneal_restart(base, cur, oo, &mut ws, &mut keep);
            cur = c2;
            cost = q + r - NIN;
            if !keep.is_empty() {
                let mut s = String::new();
                for (c, q) in &keep {
                    s += &format!("{sigma} {:04x} {:04x} {:04x} {q}\n", c[0].0, c[1].0, c[2].0);
                }
                let _g = cands_lock.lock().unwrap();
                use std::io::Write;
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(format!("{outdir}/cands.txt")).unwrap();
                f.write_all(s.as_bytes()).unwrap();
            }
        }
        for _ in 0..if oo.anneal > 0 { 0 } else { oo.sweeps } {
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

// ------------------------------------------------- exact helper search
//
// A program for target set T costs |T| + h where h counts signals that
// are not targets ("helpers").  Given the signals present, any target
// that is the XOR of two of them can be added at cost 1 and never hurts,
// so the state after adding helpers x1..xh is the closure of
// inputs + {x_i} under "add every target that is a pair sum".  Helper x_i
// must be a pair sum of the closure at its time.  Iterative deepening on
// h decides the exact optimum for small overheads.  Adjacent helpers both
// available at the earlier level are taken in increasing order (any
// solution can be bubble-sorted into that form), and the last helper
// must put some remaining target at distance one.

fn bset(b: &[u64], v: u16) -> bool {
    (b[v as usize >> 6] >> (v & 63)) & 1 == 1
}
fn bput(b: &mut [u64], v: u16) {
    b[v as usize >> 6] |= 1 << (v & 63);
}

fn closure(inc: &mut [u64], cl: &mut Vec<u16>, rem: &mut Vec<u16>) {
    loop {
        let mut changed = false;
        let mut i = 0;
        while i < rem.len() {
            let t = rem[i];
            if cl.iter().any(|&c| bset(inc, t ^ c)) {
                bput(inc, t);
                cl.push(t);
                rem.swap_remove(i);
                changed = true;
            } else {
                i += 1;
            }
        }
        if !changed {
            break;
        }
    }
}

fn pairsums(cl: &[u16]) -> Vec<u64> {
    let mut ps = vec![0u64; NV / 64];
    for i in 0..cl.len() {
        for j in (i + 1)..cl.len() {
            bput(&mut ps, cl[i] ^ cl[j]);
        }
    }
    ps
}

/// candidates ordered by how many remaining targets they make pair sums
fn helper_cands(inc: &[u64], cl: &[u16], rem: &[u16], ps: &[u64], last: bool) -> Vec<u16> {
    let mut v = helper_cands_raw(inc, cl, rem, ps, last);
    let score = |x: u16| rem.iter().filter(|&&t| bset(inc, t ^ x)).count();
    let mut sc: Vec<(usize, u16)> = v.iter().map(|&x| (score(x), x)).collect();
    sc.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    v.clear();
    v.extend(sc.into_iter().map(|(_, x)| x));
    v
}

fn helper_cands_raw(inc: &[u64], cl: &[u16], rem: &[u16], ps: &[u64], last: bool) -> Vec<u16> {
    let mut seen = vec![0u64; NV / 64];
    let mut out = Vec::new();
    if last {
        for &t in rem {
            for &c in cl {
                let x = t ^ c;
                if x != 0 && bset(ps, x) && !bset(inc, x) && !bset(&seen, x) {
                    bput(&mut seen, x);
                    out.push(x);
                }
            }
        }
    } else {
        for v in 1..NV {
            let x = v as u16;
            if bset(ps, x) && !bset(inc, x) {
                out.push(x);
            }
        }
    }
    out
}

thread_local! {
    static DEADLINE: std::cell::Cell<Option<std::time::Instant>> = const { std::cell::Cell::new(None) };
    static TIMED_OUT: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

static GLOBAL_DEADLINE_MS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
static GLOBAL_TIMED_OUT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

fn epoch_ms() -> u64 {
    std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_millis() as u64
}

fn past_deadline() -> bool {
    let g = GLOBAL_DEADLINE_MS.load(std::sync::atomic::Ordering::Relaxed);
    if g != 0 && epoch_ms() > g {
        GLOBAL_TIMED_OUT.store(true, std::sync::atomic::Ordering::Relaxed);
        return true;
    }
    DEADLINE.with(|d| d.get()).is_some_and(|t| std::time::Instant::now() > t)
}

/// Single-threaded exact search with a time cap: Ok(Some((cost, helpers)))
/// if found within targets + hmax, Ok(None) if proved impossible, Err(h)
/// on timeout with levels below h proved impossible.
fn exact_seq(targets: &[u16], hmax: usize, cap: f64) -> Result<Option<(usize, Vec<u16>)>, usize> {
    DEADLINE.with(|d| d.set(Some(std::time::Instant::now() + std::time::Duration::from_secs_f64(cap))));
    TIMED_OUT.with(|f| f.set(false));
    let mut t: Vec<u16> = targets.iter().copied().filter(|&x| x.count_ones() > 1).collect();
    t.sort_unstable();
    t.dedup();
    let mut inc = vec![0u64; NV / 64];
    let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
    for &c in &cl {
        bput(&mut inc, c);
    }
    let mut rem = t.clone();
    closure(&mut inc, &mut cl, &mut rem);
    let nodes = std::sync::atomic::AtomicU64::new(0);
    let mut out = Ok(None);
    for h in 0..=hmax {
        let found = exact_level(&inc, &cl, &rem, h, false, &nodes);
        if TIMED_OUT.with(|f| f.get()) {
            out = Err(h);
            break;
        }
        if let Some(hs) = found {
            out = Ok(Some((t.len() + h, hs)));
            break;
        }
    }
    DEADLINE.with(|d| d.set(None));
    out
}

fn exact_dfs(
    inc: &[u64],
    cl: &[u16],
    rem: &[u16],
    k: usize,
    prev: Option<(u16, &[u64])>,
    nodes: &std::sync::atomic::AtomicU64,
) -> Option<Vec<u16>> {
    nodes.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if past_deadline() {
        TIMED_OUT.with(|f| f.set(true));
        return None;
    }
    if rem.is_empty() {
        return Some(Vec::new());
    }
    if k == 0 {
        return None;
    }
    let ps = pairsums(cl);
    for x in helper_cands(inc, cl, rem, &ps, k == 1) {
        if let Some((hp, pps)) = prev {
            if bset(pps, x) && x < hp {
                continue;
            }
        }
        let (mut inc2, mut cl2, mut rem2) = (inc.to_vec(), cl.to_vec(), rem.to_vec());
        bput(&mut inc2, x);
        cl2.push(x);
        closure(&mut inc2, &mut cl2, &mut rem2);
        if k == 1 && !rem2.is_empty() {
            continue;
        }
        if let Some(mut hs) = exact_dfs(&inc2, &cl2, &rem2, k - 1, Some((x, &ps)), nodes) {
            hs.insert(0, x);
            return Some(hs);
        }
    }
    None
}

// ---- exact core v2: in-place state with undo, incremental closure,
// full canonical helper order (each helper SET is enumerated once, in
// "smallest available first" order: x_j available when x_i was chosen,
// i < j, forces x_i < x_j), candidates from pairs, stamp arrays.

const MAXD: usize = 16;

struct ExactWs {
    stamp: Vec<u32>,
    tick: u32,
    ps: Vec<Vec<u32>>,
    pstick: [u32; MAXD],
}

impl ExactWs {
    fn new() -> ExactWs {
        ExactWs { stamp: vec![0; NV], tick: 0, ps: (0..MAXD).map(|_| vec![0; NV]).collect(), pstick: [0; MAXD] }
    }
    fn mark_ps(&mut self, depth: usize, cl: &[u16]) {
        self.pstick[depth] += 1;
        let pt = self.pstick[depth];
        let row = &mut self.ps[depth];
        for i in 0..cl.len() {
            let a = cl[i];
            for &b in &cl[i + 1..] {
                row[(a ^ b) as usize] = pt;
            }
        }
    }
    fn in_ps(&self, depth: usize, x: u16) -> bool {
        self.ps[depth][x as usize] == self.pstick[depth]
    }
}

fn bclear(b: &mut [u64], v: u16) {
    b[v as usize >> 6] &= !(1 << (v & 63));
}

/// add x to a closed state and cascade: only targets using a new signal as
/// an operand can become pair sums
fn closure_add(inc: &mut [u64], cl: &mut Vec<u16>, rem: &mut Vec<u16>, x: u16) {
    bput(inc, x);
    cl.push(x);
    let mut q = cl.len() - 1;
    while q < cl.len() {
        let s = cl[q];
        q += 1;
        let mut i = 0;
        while i < rem.len() {
            let tt = rem[i];
            if bset(inc, tt ^ s) {
                bput(inc, tt);
                cl.push(tt);
                rem.swap_remove(i);
            } else {
                i += 1;
            }
        }
    }
}

fn closure_undo(inc: &mut [u64], cl: &mut Vec<u16>, rem: &mut Vec<u16>, len0: usize) {
    for idx in (len0..cl.len()).rev() {
        let v = cl[idx];
        bclear(inc, v);
        if idx > len0 {
            rem.push(v);
        }
    }
    cl.truncate(len0);
}

fn cands_v2(inc: &[u64], cl: &[u16], rem: &[u16], depth: usize, last: bool, ws: &mut ExactWs, path: &[(u16, usize)]) -> Vec<u16> {
    ws.tick = ws.tick.wrapping_add(1);
    if ws.tick == 0 {
        ws.stamp.iter_mut().for_each(|s| *s = 0);
        ws.tick = 1;
    }
    let tk = ws.tick;
    let mut out = Vec::new();
    if last {
        for &tt in rem {
            for &c in cl {
                let x = tt ^ c;
                if ws.stamp[x as usize] != tk && ws.in_ps(depth, x) && !bset(inc, x) {
                    ws.stamp[x as usize] = tk;
                    out.push(x);
                }
            }
        }
    } else {
        for i in 0..cl.len() {
            let a = cl[i];
            for &b in &cl[i + 1..] {
                let x = a ^ b;
                if ws.stamp[x as usize] != tk && !bset(inc, x) {
                    ws.stamp[x as usize] = tk;
                    out.push(x);
                }
            }
        }
    }
    out.retain(|&x| path.iter().all(|&(xi, di)| !(x < xi && ws.in_ps(di, x))));
    if !last {
        let mut sc: Vec<(usize, u16)> = out.iter().map(|&x| (rem.iter().filter(|&&tt| bset(inc, tt ^ x)).count(), x)).collect();
        sc.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
        out = sc.into_iter().map(|(_, x)| x).collect();
    }
    out
}

#[allow(clippy::too_many_arguments)]
fn dfs_v2(
    inc: &mut [u64],
    cl: &mut Vec<u16>,
    rem: &mut Vec<u16>,
    k: usize,
    depth: usize,
    path: &mut Vec<(u16, usize)>,
    ws: &mut ExactWs,
    nodes: &std::sync::atomic::AtomicU64,
) -> Option<Vec<u16>> {
    nodes.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    if past_deadline() {
        TIMED_OUT.with(|f| f.set(true));
        return None;
    }
    if rem.is_empty() {
        return Some(Vec::new());
    }
    if k == 0 || depth >= MAXD {
        return None;
    }
    ws.mark_ps(depth, cl);
    for x in cands_v2(inc, cl, rem, depth, k == 1, ws, path) {
        let len0 = cl.len();
        closure_add(inc, cl, rem, x);
        if k == 1 {
            let ok = rem.is_empty();
            closure_undo(inc, cl, rem, len0);
            if ok {
                return Some(vec![x]);
            }
            continue;
        }
        path.push((x, depth));
        let r = dfs_v2(inc, cl, rem, k - 1, depth + 1, path, ws, nodes);
        path.pop();
        closure_undo(inc, cl, rem, len0);
        if let Some(mut hs) = r {
            hs.insert(0, x);
            return Some(hs);
        }
        if TIMED_OUT.with(|f| f.get()) {
            return None;
        }
    }
    None
}

/// one depth h of the exact search from a closed state; parallel over the
/// first helper when `par`
fn exact_level(inc: &[u64], cl: &[u16], rem: &[u16], h: usize, par: bool, nodes: &std::sync::atomic::AtomicU64) -> Option<Vec<u16>> {
    if rem.is_empty() {
        return Some(Vec::new());
    }
    if h == 0 {
        return None;
    }
    let mut ws0 = ExactWs::new();
    ws0.mark_ps(0, cl);
    let tops = cands_v2(inc, cl, rem, 0, h == 1, &mut ws0, &[]);
    let run = |x: u16, ws: &mut ExactWs| -> Option<Vec<u16>> {
        ws.mark_ps(0, cl);
        let (mut inc2, mut cl2, mut rem2) = (inc.to_vec(), cl.to_vec(), rem.to_vec());
        closure_add(&mut inc2, &mut cl2, &mut rem2, x);
        if h == 1 {
            return rem2.is_empty().then(|| vec![x]);
        }
        let mut path = vec![(x, 0usize)];
        dfs_v2(&mut inc2, &mut cl2, &mut rem2, h - 1, 1, &mut path, ws, nodes).map(|mut hs| {
            hs.insert(0, x);
            hs
        })
    };
    if par {
        tops.par_iter().map_init(ExactWs::new, |ws, &x| run(x, ws)).find_map_any(|r| r)
    } else {
        let mut ws = ws0;
        for &x in &tops {
            if let Some(r) = run(x, &mut ws) {
                return Some(r);
            }
            if TIMED_OUT.with(|f| f.get()) {
                return None;
            }
        }
        None
    }
}

/// Exact minimum for small overheads: returns (cost, helpers) or None if
/// no program with at most |T| + hmax XORs exists.
fn exact(targets: &[u16], hmax: usize) -> Option<(usize, Vec<u16>)> {
    let mut t: Vec<u16> = targets.iter().copied().filter(|&x| x.count_ones() > 1).collect();
    t.sort_unstable();
    t.dedup();
    let mut inc = vec![0u64; NV / 64];
    let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
    for &c in &cl {
        bput(&mut inc, c);
    }
    let mut rem = t.clone();
    closure(&mut inc, &mut cl, &mut rem);
    println!("  {} targets, {} reachable with no helper", t.len(), t.len() - rem.len());
    for h in 0..=hmax {
        let t0 = std::time::Instant::now();
        let nodes = std::sync::atomic::AtomicU64::new(0);
        let found = exact_level(&inc, &cl, &rem, h, true, &nodes);
        println!(
            "  h = {h}: {}  ({} nodes, {:.1}s)",
            if found.is_some() { "FOUND" } else { "impossible" },
            nodes.load(std::sync::atomic::Ordering::Relaxed),
            t0.elapsed().as_secs_f64()
        );
        if let Some(hs) = found {
            return Some((t.len() + h, hs));
        }
    }
    None
}

// ------------------------------------------------- helper-pool LNS
//
// Large-neighbourhood search around BP solutions: keep f of a solution's
// helpers as "extras" (added, at cost 1 each, whenever they become pair
// sums -- like targets), and search the rest exactly with depth D.  A
// hit needs one helper fewer than the best BP solution.

/// Replay a solution: targets and extras join whenever they are pair
/// sums; the free helpers join in order when stuck.  Returns the program
/// or None if the helpers do not complete it.
fn replay(targets: &[u16], extras: &[u16], free: &[u16]) -> Option<Prog> {
    let mut st = St::new();
    let mut rng = Rng(7);
    let mut want: Vec<u16> = targets.iter().chain(extras).copied().filter(|&t| t.count_ones() > 1).collect();
    want.sort_unstable();
    want.dedup();
    let mut fi = 0;
    loop {
        let mut progress = true;
        while progress {
            progress = false;
            let mut i = 0;
            while i < want.len() {
                let t = want[i];
                if st.has(t) {
                    want.swap_remove(i);
                    continue;
                }
                if st.val.iter().any(|&c| st.has(t ^ c) && (t ^ c) != c) {
                    st.add(t, &mut rng);
                    want.swap_remove(i);
                    progress = true;
                } else {
                    i += 1;
                }
            }
        }
        if targets.iter().all(|&t| t == 0 || st.has(t)) {
            return Some(dce(&st.prog(), targets));
        }
        if fi == free.len() {
            return None;
        }
        let x = free[fi];
        fi += 1;
        if !st.val.iter().any(|&c| st.has(x ^ c) && (x ^ c) != c) {
            return None;
        }
        st.add(x, &mut rng);
    }
}

fn lns(targets: &[u16], o: &Opts, depth: usize, maxsub: usize) -> Option<Prog> {
    let mut t: Vec<u16> = targets.iter().copied().filter(|&x| x.count_ones() > 1).collect();
    t.sort_unstable();
    t.dedup();
    let tset: std::collections::HashSet<u16> = t.iter().copied().collect();
    // pool of distinct BP helper sets
    let sols: Vec<Prog> = (0..o.runs)
        .into_par_iter()
        .map(|r| {
            let mut rng = Rng(o.seed ^ (r as u64).wrapping_mul(0xA24B_AED4_963E_E407));
            dce(&bp_run(targets, &mut rng, o.prm), targets)
        })
        .collect();
    let best = sols.iter().map(|p| p.xors()).min().unwrap();
    let goal = best - 1;
    let mut hsets: Vec<Vec<u16>> = sols
        .iter()
        .filter(|p| p.xors() <= best + 1)
        .map(|p| {
            let mut h: Vec<u16> = p.val[NIN..].iter().copied().filter(|v| !tset.contains(v)).collect();
            h.sort_unstable();
            h
        })
        .collect();
    hsets.sort();
    hsets.dedup();
    let budget = goal - t.len(); // helpers allowed
    println!("  {} targets, BP best {best}; {} distinct helper sets; goal {goal} = {} helpers", t.len(), hsets.len(), budget);
    if budget < depth {
        return exact(&t, budget).and_then(|(_, hs)| replay(&t, &[], &hs));
    }
    let f = budget - depth;
    // (helper set, subset) work items; subsets sampled when too many
    let mut items: Vec<Vec<u16>> = Vec::new();
    let mut rng = Rng(o.seed);
    for h in &hsets {
        if h.len() < f {
            continue;
        }
        let total = binom(h.len(), f);
        if total <= maxsub as f64 {
            for comb in combos(h.len(), f) {
                items.push(comb.iter().map(|&i| h[i]).collect());
            }
        } else {
            for _ in 0..maxsub {
                let mut idx: Vec<usize> = (0..h.len()).collect();
                for i in 0..f {
                    let j = i + rng.below(h.len() - i);
                    idx.swap(i, j);
                }
                items.push(idx[..f].iter().map(|&i| h[i]).collect());
            }
        }
    }
    items.sort();
    items.dedup();
    println!("  {} (fixed-subset) neighbourhoods of {} kept helpers, exact depth {depth}", items.len(), f);
    let nodes = std::sync::atomic::AtomicU64::new(0);
    let hit = items.par_iter().find_map_any(|ex| {
        let mut inc = vec![0u64; NV / 64];
        let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
        for &c in &cl {
            bput(&mut inc, c);
        }
        let mut rem: Vec<u16> = t.iter().chain(ex.iter()).copied().collect();
        closure(&mut inc, &mut cl, &mut rem);
        let added = ex.iter().filter(|&&x| bset(&inc, x)).count();
        let rem_t: Vec<u16> = rem.iter().copied().filter(|v| tset.contains(v)).collect();
        let d = budget - added;
        let free = exact_dfs(&inc, &cl, &rem_t, d, None, &nodes)?;
        let used: Vec<u16> = ex.iter().copied().filter(|&x| bset(&inc, x)).collect();
        replay(&t, &used, &free)
    });
    println!("  {} nodes", nodes.load(std::sync::atomic::Ordering::Relaxed));
    hit
}

// ------------------------------------------------- exhaustive orbit scan
//
// The 3x3 orbitscan.py idea at 4x4.  Side costs depend on two sandwich
// factors each -- L on (X, Y), R on (Y, Z), P on (Z, X) -- and are
// unchanged when a factor is multiplied on the right by a permutation
// matrix (that only permutes the rows or columns of every target, i.e.
// relabels the inputs).  So X, Y, Z range over the 840 right cosets of
// the permutation matrices in GL(4,2); three 840 x 840 side tables (BP
// costs) and a min-plus pass over all 840^3 triples cover the whole
// orbit.  The slot symmetries only permute and transpose the three
// families, which a relabelling undoes, so the plain variant suffices.

fn perm_mats() -> Vec<u16> {
    let mut out = Vec::new();
    for a in 0..4 {
        for b in 0..4 {
            for c in 0..4 {
                for d in 0..4 {
                    let p = [a, b, c, d];
                    let mut s = [false; 4];
                    if p.iter().all(|&v| !std::mem::replace(&mut s[v], true)) {
                        out.push((0..4).fold(0u16, |m, i| m | (1 << (4 * i + p[i]))));
                    }
                }
            }
        }
    }
    out
}

/// right-coset representatives X.S4 of GL(4,2) (minimum u16 of each coset)
fn coset_reps(g: &[(u16, u16)]) -> Vec<(u16, u16)> {
    let perms = perm_mats();
    assert_eq!(perms.len(), 24);
    let inv: HashMap<u16, u16> = g.iter().copied().collect();
    let mut reps: Vec<u16> = g
        .iter()
        .map(|&(x, _)| perms.iter().map(|&q| m_mul(x, q)).min().unwrap())
        .collect();
    reps.sort_unstable();
    reps.dedup();
    reps.into_iter().map(|x| (x, inv[&x])).collect()
}

fn scan(pre: &str, o: &Opts) {
    let s0 = Scheme::from_sms(pre);
    assert!(s0.brent_ok(), "input scheme fails Brent");
    let g = gl42();
    let reps = coset_reps(&g);
    let n = reps.len();
    assert_eq!(n, 840, "expected 840 right cosets");
    // invariance gate: a permutation on the right of any factor keeps every side cost
    {
        let perms = perm_mats();
        let mut ws = Ws::new(o.seed);
        let gp = Params { slack: 0, p: 0.0, pilot: 0 };
        let mut rng = Rng(o.seed ^ 77);
        for _ in 0..5 {
            let (x, y) = (reps[rng.below(n)], reps[rng.below(n)]);
            let q = perms[rng.below(24)];
            let xq = (m_mul(x.0, q), m_mul(m_t(q), x.1)); // (XQ)^-1 = Q^T X^-1
            let side = |x: (u16, u16), ws: &mut Ws| {
                let t: Vec<u16> = s0.u.iter().map(|&m| m_mul(m_mul(m_t(x.0), m), m_t(y.1))).collect();
                let mut tt: Vec<u16> = t.iter().copied().filter(|v| v.count_ones() > 1).collect();
                tt.sort_unstable();
                tt.dedup();
                (tt.len(), ws.bp(&t, 8, gp).xors())
            };
            let (a, b) = (side(x, &mut ws), side(xq, &mut ws));
            assert_eq!(a.0, b.0, "coset invariance gate failed (target count)");
            assert!(a.1.abs_diff(b.1) <= 1, "coset invariance gate failed (BP cost {} vs {})", a.1, b.1);
        }
    }
    let t0 = std::time::Instant::now();
    let gp = Params { slack: 0, p: 0.0, pilot: 0 };
    let runs = o.runs.max(1);
    // T_U[x][y] = cost{X^T U Y^-T}, T_V[y][z] = cost{Y^T V Z^-T}, T_W[z][x] = cost{X^-1 W Z}
    let table = |fam: &Vec<u16>, which: usize| -> Vec<u8> {
        let rows: Vec<Vec<u8>> = (0..n)
            .into_par_iter()
            .map(|i| {
                let mut ws = Ws::new(o.seed ^ ((which * n + i) as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15));
                (0..n)
                    .map(|j| {
                        let t: Vec<u16> = fam
                            .iter()
                            .map(|&m| match which {
                                0 => m_mul(m_mul(m_t(reps[i].0), m), m_t(reps[j].1)),
                                1 => m_mul(m_mul(m_t(reps[i].0), m), m_t(reps[j].1)),
                                _ => m_mul(m_mul(reps[j].1, m), reps[i].0),
                            })
                            .collect();
                        ws.bp(&t, runs, gp).xors().min(255) as u8
                    })
                    .collect()
            })
            .collect();
        rows.concat()
    };
    let tu = table(&s0.u, 0); // [x][y]
    println!("  U table done ({:.0}s)", t0.elapsed().as_secs_f64());
    let tv = table(&s0.v, 1); // [y][z]
    println!("  V table done ({:.0}s)", t0.elapsed().as_secs_f64());
    let tw = table(&s0.w, 2); // [z][x]
    println!("  W table done ({:.0}s)", t0.elapsed().as_secs_f64());
    let r = s0.u.len();
    // min-plus over all triples, parallel over x
    let res: Vec<(u32, Vec<(usize, usize, usize)>)> = (0..n)
        .into_par_iter()
        .map(|x| {
            let mut best = u32::MAX;
            let mut keep = Vec::new();
            for y in 0..n {
                let a = tu[x * n + y] as u32;
                for z in 0..n {
                    let s = a + tv[y * n + z] as u32 + tw[z * n + x] as u32;
                    if s < best {
                        best = s;
                        keep.clear();
                    }
                    if s <= best + o.depth as u32 && keep.len() < 2000 {
                        keep.push((x, y, z));
                    }
                }
            }
            (best, keep)
        })
        .collect();
    let gbest = res.iter().map(|r| r.0).min().unwrap();
    let mut hist: HashMap<u32, usize> = HashMap::new();
    for (b, _) in &res {
        *hist.entry(*b).or_default() += 1;
    }
    let mut hv: Vec<_> = hist.into_iter().collect();
    hv.sort();
    println!(
        "orbit minimum (BP x{runs} side costs): {} = sides + {}; per-X minima histogram {:?}  ({:.0}s)",
        gbest as usize + r - NIN,
        r - NIN,
        hv.iter().map(|(b, c)| (*b as usize + r - NIN, *c)).collect::<Vec<_>>(),
        t0.elapsed().as_secs_f64()
    );
    let outdir = o.out.clone().unwrap_or_else(|| ".".into());
    std::fs::create_dir_all(&outdir).unwrap();
    let mut s = String::new();
    let mut cnt = 0;
    for (_, keep) in &res {
        for &(x, y, z) in keep {
            let tot = tu[x * n + y] as u32 + tv[y * n + z] as u32 + tw[z * n + x] as u32;
            if tot <= gbest + o.depth as u32 {
                s += &format!("0 {:04x} {:04x} {:04x} {}\n", reps[x].0, reps[y].0, reps[z].0, tot as usize + r - NIN);
                cnt += 1;
            }
        }
    }
    std::fs::write(format!("{outdir}/scan_cands.txt"), s).unwrap();
    // tables for reuse
    let mut raw = Vec::with_capacity(3 * n * n);
    raw.extend_from_slice(&tu);
    raw.extend_from_slice(&tv);
    raw.extend_from_slice(&tw);
    std::fs::write(format!("{outdir}/scan_tables.u8"), raw).unwrap();
    println!("wrote {cnt} candidate triples within +{} of the minimum to {outdir}/scan_cands.txt", o.depth);
}

/// Batch orbit screen: for each .bits scheme (anf.rs order: alpha, beta,
/// gamma blocks of 16 bits each), a few short annealing chains from random
/// orbit points; prints the best BP total per scheme.  Parallel over schemes.
fn screen(list: &str, o: &Opts, steps: usize, chains: usize) {
    let names: Vec<String> = std::fs::read_to_string(list).unwrap().lines().map(|s| s.trim().to_string()).filter(|s| !s.is_empty()).collect();
    let g = gl42();
    let oo = OrbitOpts { restarts: chains, sweeps: 0, topk: 0, final_runs: 16, anneal: steps, t0: 2.0, t1: 0.2, collect: 0 };
    let done = std::sync::atomic::AtomicUsize::new(0);
    let out = std::sync::Mutex::new(Vec::new());
    names.par_iter().enumerate().for_each(|(i, nm)| {
        let txt = std::fs::read_to_string(nm).unwrap();
        let b: Vec<u8> = txt.trim().bytes().map(|c| c - b'0').collect();
        assert_eq!(b.len() % 48, 0, "{nm}: not a 4x4x4 bits file");
        let r = b.len() / 48;
        let blk = |off: usize, m: usize| (0..16).fold(0u16, |a, k| a | ((b[off + 16 * m + k] as u16) << k));
        let s0 = Scheme {
            u: (0..r).map(|m| blk(0, m)).collect(),
            v: (0..r).map(|m| blk(16 * r, m)).collect(),
            w: (0..r).map(|m| blk(32 * r, m)).collect(),
        };
        if !s0.brent_ok() {
            println!("{nm}: FAILS Brent, skipped");
            return;
        }
        let mut ws = Ws::new(o.seed ^ (i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut best = (usize::MAX, 0usize, [(0u16, 0u16); 3]);
        for _ in 0..chains {
            let sg = ws.rng.below(6);
            let base = s0.sym(sg);
            let st = [g[ws.rng.below(g.len())], g[ws.rng.below(g.len())], g[ws.rng.below(g.len())]];
            let mut keep = Vec::new();
            let (cur, _) = anneal_restart(&base, st, &oo, &mut ws, &mut keep);
            let (c, _) = scheme_cost(&base.act(cur[0], cur[1], cur[2]), &mut ws, oo.final_runs, Params { slack: 0, p: 0.0, pilot: 0 });
            if c < best.0 {
                best = (c, sg, cur);
            }
        }
        let k = done.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
        println!("{nm} best {} (sigma {} X {:04x} Y {:04x} Z {:04x})  [{k}/{}]", best.0, best.1, best.2[0].0, best.2[1].0, best.2[2].0, names.len());
        out.lock().unwrap().push((best.0, nm.clone()));
    });
    let mut v = out.into_inner().unwrap();
    v.sort();
    let mut hist: std::collections::BTreeMap<usize, usize> = std::collections::BTreeMap::new();
    for (c, _) in &v {
        *hist.entry(*c).or_default() += 1;
    }
    println!("screen done: histogram {:?}", hist);
    if let Some(f) = &o.out {
        std::fs::write(f, v.iter().map(|(c, n)| format!("{c} {n}\n")).collect::<String>()).unwrap();
    }
}

/// Exact refinement of collected orbit points: per side, BP with
/// o.runs restarts, then an exact search one helper below BP (time cap
/// o.cap per side).  Writes the best point's sms + programs.
fn refine(pre: &str, cands: &str, o: &Opts) {
    let s0 = Scheme::from_sms(pre);
    assert!(s0.brent_ok(), "input scheme fails Brent");
    let syms: Vec<Scheme> = (0..6).map(|i| s0.sym(i)).collect();
    let g = gl42();
    let inv: HashMap<u16, u16> = g.iter().copied().collect();
    let mut pts: Vec<(usize, u16, u16, u16, usize)> = std::fs::read_to_string(cands)
        .unwrap()
        .lines()
        .filter_map(|l| {
            let f: Vec<&str> = l.split_whitespace().collect();
            if f.len() < 5 {
                return None;
            }
            Some((
                f[0].parse().ok()?,
                u16::from_str_radix(f[1], 16).ok()?,
                u16::from_str_radix(f[2], 16).ok()?,
                u16::from_str_radix(f[3], 16).ok()?,
                f[4].parse().ok()?,
            ))
        })
        .collect();
    pts.sort_by_key(|p| p.4);
    pts.dedup_by_key(|p| (p.0, p.1, p.2, p.3));
    println!("{} candidate points", pts.len());
    let outdir = o.out.clone().unwrap_or_else(|| ".".into());
    std::fs::create_dir_all(&outdir).unwrap();
    let best = std::sync::Mutex::new(usize::MAX);
    let r = s0.u.len();
    // side results keyed by the sorted distinct non-unit target set
    type SideRes = (usize, Prog, String);
    let cache: std::sync::Mutex<HashMap<Vec<u16>, SideRes>> = std::sync::Mutex::new(HashMap::new());
    let hits = std::sync::atomic::AtomicUsize::new(0);
    pts.par_iter().enumerate().for_each(|(i, &(sg, x, y, z, q))| {
        let s = syms[sg].act((x, inv[&x]), (y, inv[&y]), (z, inv[&z]));
        let mut ws = Ws::new(o.seed ^ (i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15));
        let mut parts = Vec::new();
        let mut total = r - NIN;
        let mut progs = Vec::new();
        for m in [&s.u, &s.v, &s.w] {
            let mut tset: Vec<u16> = m.iter().copied().filter(|&v| v.count_ones() > 1).collect();
            tset.sort_unstable();
            tset.dedup();
            if let Some((c, p, tg)) = cache.lock().unwrap().get(&tset).cloned() {
                hits.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                total += c;
                parts.push(format!("{c}{tg}"));
                progs.push(p);
                continue;
            }
            let bp = ws.bp(m, o.runs, o.prm);
            let over = bp.xors() - tset.len();
            let (cost, prog, tag) = if over == 0 {
                (bp.xors(), bp, "=".to_string())
            } else {
                match exact_seq(m, over - 1, o.cap) {
                    Ok(Some((c, hs))) => {
                        let p = replay(m, &[], &hs).expect("replay");
                        assert_eq!(p.xors(), c);
                        (c, p, "!".to_string())
                    }
                    Ok(None) => (bp.xors(), bp, "=".to_string()),
                    Err(h) => (bp.xors(), bp, format!("?{}", tset.len() + h)),
                }
            };
            cache.lock().unwrap().insert(tset, (cost, prog.clone(), tag.clone()));
            total += cost;
            parts.push(format!("{cost}{tag}"));
            progs.push(prog);
        }
        let mut b = best.lock().unwrap();
        let tag = if total < *b { " NEW BEST" } else { "" };
        println!("point {sg} {x:04x} {y:04x} {z:04x} (quick {q}): L {} R {} Pt {} -> total {total}{tag}", parts[0], parts[1], parts[2]);
        if total < *b {
            *b = total;
            assert!(s.brent_ok());
            let p = format!("{outdir}/refined_{total}");
            s.write_sms(&p);
            std::fs::write(format!("{p}_L.slp"), emit_direct(&progs[0], &s.u).0).unwrap();
            std::fs::write(format!("{p}_R.slp"), emit_direct(&progs[1], &s.v).0).unwrap();
            std::fs::write(format!("{p}_P.slp"), emit_transposed(&progs[2], &s.w).0).unwrap();
        }
    });
    println!("best {}  (side cache hits {})", best.lock().unwrap(), hits.load(std::sync::atomic::Ordering::Relaxed));
}

// ------------------------------------------------- whole-orbit lower bounds
//
// `scan` scores every coset pair with Boyar-Peralta (upper bounds);
// `lbscan` proves lower bounds on all of them.  A side with targets T
// costs |T| + h (h = helpers), and refuting one more helper level raises
// its bound by one.  A coset triple can cost less than `target` only if
// its three lower bounds allow it, so levels are refuted only for target
// sets that sit in such a triple, lowest level first, until no triple is
// left (a proof for the whole orbit), or the triples left have only exact
// sides (genuine points below `target`) or sides the search could not
// decide within the cap and depth.

struct LbSet {
    key: Vec<u16>,
    lev: u8,
    exact: bool,
    stuck: bool,
}

/// One helper level of the exact search on the calling thread, with a time
/// cap: Some(true) if |T| + h XORs suffice, Some(false) if refuted, None on
/// timeout.  Lower levels must already be refuted.
fn level_test(key: &[u16], h: usize, cap: f64, ws: &mut ExactWs) -> Option<bool> {
    let mut inc = vec![0u64; NV / 64];
    let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
    for &c in &cl {
        bput(&mut inc, c);
    }
    let mut rem = key.to_vec();
    closure(&mut inc, &mut cl, &mut rem);
    if rem.is_empty() {
        return Some(true);
    }
    if h == 0 {
        return Some(false);
    }
    DEADLINE.with(|d| d.set(Some(std::time::Instant::now() + std::time::Duration::from_secs_f64(cap))));
    TIMED_OUT.with(|f| f.set(false));
    let nodes = std::sync::atomic::AtomicU64::new(0);
    ws.mark_ps(0, &cl);
    let tops = cands_v2(&inc, &cl, &rem, 0, h == 1, ws, &[]);
    let mut found = false;
    for &x in &tops {
        ws.mark_ps(0, &cl);
        let len0 = cl.len();
        closure_add(&mut inc, &mut cl, &mut rem, x);
        let ok = if h == 1 {
            rem.is_empty()
        } else {
            let mut path = vec![(x, 0usize)];
            dfs_v2(&mut inc, &mut cl, &mut rem, h - 1, 1, &mut path, ws, &nodes).is_some()
        };
        closure_undo(&mut inc, &mut cl, &mut rem, len0);
        if ok {
            found = true;
            break;
        }
        if TIMED_OUT.with(|f| f.get()) {
            break;
        }
    }
    let to = TIMED_OUT.with(|f| f.get());
    DEADLINE.with(|d| d.set(None));
    if found {
        Some(true)
    } else if to {
        None
    } else {
        Some(false)
    }
}

/// level_test with the search itself parallel (one set at a time, global
/// deadline), for batches too small to keep the threads busy.
fn level_test_par(key: &[u16], h: usize, cap: f64) -> Option<bool> {
    let mut inc = vec![0u64; NV / 64];
    let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
    for &c in &cl {
        bput(&mut inc, c);
    }
    let mut rem = key.to_vec();
    closure(&mut inc, &mut cl, &mut rem);
    if rem.is_empty() {
        return Some(true);
    }
    if h == 0 {
        return Some(false);
    }
    GLOBAL_TIMED_OUT.store(false, std::sync::atomic::Ordering::Relaxed);
    GLOBAL_DEADLINE_MS.store(epoch_ms() + (cap * 1000.0) as u64, std::sync::atomic::Ordering::Relaxed);
    let nodes = std::sync::atomic::AtomicU64::new(0);
    let found = exact_level(&inc, &cl, &rem, h, true, &nodes);
    GLOBAL_DEADLINE_MS.store(0, std::sync::atomic::Ordering::Relaxed);
    let to = GLOBAL_TIMED_OUT.load(std::sync::atomic::Ordering::Relaxed);
    match found {
        Some(_) => Some(true),
        None if to => None,
        None => Some(false),
    }
}

fn lbscan(pre: &str, o: &Opts) {
    let s0 = Scheme::from_sms(pre);
    assert!(s0.brent_ok(), "input scheme fails Brent");
    let r = s0.u.len();
    assert!(o.target > r - NIN, "lbscan needs --target T: prove every orbit point costs at least T");
    let goal = (o.target - (r - NIN)) as u16; // what the three side costs must reach together
    let g = gl42();
    let reps = coset_reps(&g);
    let n = reps.len();
    assert_eq!(n, 840, "expected 840 right cosets");
    let t0 = std::time::Instant::now();
    let el = || t0.elapsed().as_secs_f64();
    let fams = [&s0.u, &s0.v, &s0.w];
    // same layout as scan: U[x][y] = {X^T U Y^-T}, V[y][z] = {Y^T V Z^-T}, W[z][x] = {X^-1 W Z}
    let targets = |which: usize, xi: (u16, u16), xj: (u16, u16)| -> Vec<u16> {
        let mut t: Vec<u16> = fams[which]
            .iter()
            .map(|&m| if which < 2 { m_mul(m_mul(m_t(xi.0), m), m_t(xj.1)) } else { m_mul(m_mul(xj.1, m), xi.0) })
            .filter(|v| v.count_ones() > 1)
            .collect();
        t.sort_unstable();
        t.dedup();
        t
    };
    // gate: a permutation on the right of either factor keeps the target count
    {
        let perms = perm_mats();
        let mut rng = Rng(o.seed ^ 91);
        for _ in 0..200 {
            let which = rng.below(3);
            let (i, j) = (rng.below(n), rng.below(n));
            let q = perms[rng.below(24)];
            let (a, b) = (reps[i], reps[j]);
            let aq = (m_mul(a.0, q), m_mul(m_t(q), a.1));
            let bq = (m_mul(b.0, q), m_mul(m_t(q), b.1));
            let base = targets(which, a, b).len();
            assert_eq!(base, targets(which, aq, b).len(), "coset gate failed (first factor)");
            assert_eq!(base, targets(which, a, bq).len(), "coset gate failed (second factor)");
        }
    }
    let mut index: HashMap<Vec<u16>, u32> = HashMap::new();
    let mut sets: Vec<LbSet> = Vec::new();
    let mut ids: Vec<Vec<u32>> = Vec::new();
    for which in 0..3 {
        let keys: Vec<Vec<u16>> = (0..n * n).into_par_iter().map(|e| targets(which, reps[e / n], reps[e % n])).collect();
        let mut tab = Vec::with_capacity(n * n);
        for t in keys {
            let id = match index.get(&t) {
                Some(&id) => id,
                None => {
                    let id = sets.len() as u32;
                    index.insert(t.clone(), id);
                    sets.push(LbSet { key: t, lev: 0, exact: false, stuck: false });
                    id
                }
            };
            tab.push(id);
        }
        let mut fl = vec![0usize; 64];
        for &id in &tab {
            fl[sets[id as usize].key.len().min(63)] += 1;
        }
        println!("side {which}: {} distinct target sets so far; floor histogram {}  ({:.0}s)", sets.len(), hist_str(&fl), el());
        ids.push(tab);
    }
    drop(index);
    // level 0: the inputs alone reach every target
    sets.par_iter_mut().for_each(|s| {
        let mut inc = vec![0u64; NV / 64];
        let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
        for &c in &cl {
            bput(&mut inc, c);
        }
        let mut rem = s.key.clone();
        closure(&mut inc, &mut cl, &mut rem);
        if rem.is_empty() {
            s.exact = true;
        } else {
            s.lev = 1;
        }
    });
    println!("level 0: {} of {} sets exact at their floor ({:.0}s)", sets.iter().filter(|s| s.exact).count(), sets.len(), el());
    // checkpoint: "id hash lev exact" per settled set; ids are deterministic for a given scheme
    let khash = |k: &[u16]| k.iter().fold(0xcbf2_9ce4_8422_2325u64 ^ k.len() as u64, |h, &v| (h ^ v as u64).wrapping_mul(0x0000_0100_0000_01b3));
    let cache_path = o.out.as_ref().map(|d| {
        std::fs::create_dir_all(d).unwrap();
        format!("{d}/lbscan_cache.txt")
    });
    if let Some(cp) = &cache_path {
        if let Ok(txt) = std::fs::read_to_string(cp) {
            let (mut used, mut bad) = (0usize, 0usize);
            for ln in txt.lines() {
                let f: Vec<&str> = ln.split_whitespace().collect();
                if f.len() != 4 {
                    continue;
                }
                let (id, h, lev, ex): (usize, u64, u8, bool) = (f[0].parse().unwrap(), u64::from_str_radix(f[1], 16).unwrap(), f[2].parse().unwrap(), f[3] == "1");
                if id < sets.len() && khash(&sets[id].key) == h {
                    let st = &mut sets[id];
                    st.lev = st.lev.max(lev);
                    st.exact |= ex;
                    used += 1;
                } else {
                    bad += 1;
                }
            }
            println!("checkpoint {cp}: {used} records applied, {bad} rejected");
        }
    }
    let budget_hit = |t: f64| o.budget > 0.0 && t > o.budget;
    // c[p][q] = min_m a[p][m] + b[m][q]
    let mp = |a: &[u8], b: &[u8]| -> Vec<u16> {
        (0..n)
            .into_par_iter()
            .flat_map_iter(|p| {
                let mut row = vec![u16::MAX; n];
                for m in 0..n {
                    let am = a[p * n + m] as u16;
                    for (q, &bv) in b[m * n..(m + 1) * n].iter().enumerate() {
                        let v = am + bv as u16;
                        if v < row[q] {
                            row[q] = v;
                        }
                    }
                }
                row
            })
            .collect()
    };
    let lb_tables = |sets: &[LbSet]| -> Vec<Vec<u8>> {
        ids.iter().map(|tab| tab.par_iter().map(|&id| (sets[id as usize].key.len() + sets[id as usize].lev as usize).min(255) as u8).collect()).collect()
    };
    let mut round = 0usize;
    loop {
        round += 1;
        let lbt = lb_tables(&sets);
        // partner minima: U[x][y] <- (V*W)[y][x], V[y][z] <- (W*U)[z][y], W[z][x] <- (U*V)[x][z]
        let part = [mp(&lbt[1], &lbt[2]), mp(&lbt[2], &lbt[0]), mp(&lbt[0], &lbt[1])];
        let mut req = vec![0u16; sets.len()];
        let mut cnt = vec![0u32; sets.len()];
        let mut deficient = [0usize; 3];
        for k in 0..3 {
            for e in 0..n * n {
                let need = goal.saturating_sub(part[k][(e % n) * n + e / n]);
                if (lbt[k][e] as u16) < need {
                    deficient[k] += 1;
                    let id = ids[k][e] as usize;
                    req[id] = req[id].max(need);
                    cnt[id] += 1;
                }
            }
        }
        let open: Vec<usize> = (0..sets.len()).filter(|&i| req[i] > 0).collect();
        let todo: Vec<usize> = open.iter().copied().filter(|&i| !sets[i].exact && !sets[i].stuck).collect();
        let cur = (0..n * n).map(|e| lbt[0][e] as usize + part[0][(e % n) * n + e / n] as usize).min().unwrap();
        println!(
            "round {round}: proved so far: every point costs >= {}; deficient entries U {} V {} W {}; deficient sets {} (exact {}, stuck {}, to raise {})  ({:.0}s)",
            cur + r - NIN, deficient[0], deficient[1], deficient[2], open.len(),
            open.iter().filter(|&&i| sets[i].exact).count(),
            open.iter().filter(|&&i| sets[i].stuck).count(),
            todo.len(), el()
        );
        if todo.is_empty() {
            break;
        }
        if budget_hit(el()) {
            println!("budget of {:.0}s reached; stopping", o.budget);
            break;
        }
        let minlev = todo.iter().map(|&i| sets[i].lev).min().unwrap();
        let mut batch: Vec<usize> = todo.into_iter().filter(|&i| sets[i].lev == minlev).collect();
        // from level 3 on, tests are costly: take the sets in the most deficient
        // entries first, a chunk at a time, and recompute needs in between
        let at_level = batch.len();
        if minlev >= 3 && batch.len() > o.chunk {
            batch.sort_by_key(|&i| (std::cmp::Reverse(cnt[i]), i));
            batch.truncate(o.chunk);
        }
        // deep tests: one at a time with the search itself parallel (most
        // deficient entries first, then fewest targets), since one raised side
        // often settles a whole triple and a single-thread search at level 5+
        // rarely finishes within the cap
        if minlev >= 5 || (minlev >= 4 && batch.len() < o.threads) {
            batch.sort_by_key(|&i| (std::cmp::Reverse(cnt[i]), sets[i].key.len(), i));
            batch.truncate(1);
        }
        if minlev as usize > o.depth {
            for &i in &batch {
                sets[i].stuck = true;
            }
            println!("  level {minlev}: {} sets beyond --depth {}, left open", batch.len(), o.depth);
            continue;
        }
        let (mut up, mut ex, mut to, mut done) = (0usize, 0usize, 0usize, 0usize);
        let tb = std::time::Instant::now();
        for chunk in batch.chunks(20_000) {
            let res: Vec<(usize, Option<bool>)> = if chunk.len() < o.threads {
                chunk.iter().map(|&i| (i, level_test_par(&sets[i].key, sets[i].lev as usize, o.cap))).collect()
            } else {
                chunk.par_iter().map_init(ExactWs::new, |ws, &i| (i, level_test(&sets[i].key, sets[i].lev as usize, o.cap, ws))).collect()
            };
            let mut log = String::new();
            for (i, rv) in res {
                match rv {
                    Some(true) => {
                        sets[i].exact = true;
                        ex += 1;
                    }
                    Some(false) => {
                        sets[i].lev += 1;
                        up += 1;
                    }
                    None => {
                        sets[i].stuck = true;
                        to += 1;
                        continue;
                    }
                }
                log += &format!("{i} {:016x} {} {}\n", khash(&sets[i].key), sets[i].lev, sets[i].exact as u8);
            }
            if let Some(cp) = &cache_path {
                use std::io::Write;
                let mut f = std::fs::OpenOptions::new().create(true).append(true).open(cp).unwrap();
                f.write_all(log.as_bytes()).unwrap();
            }
            done += chunk.len();
            if done < batch.len() {
                println!(
                    "    level {minlev}: {done}/{} ({up} refuted, {ex} exact, {to} timed out; {:.0}s, {:.1} ms/set)",
                    batch.len(), el(), 1000.0 * tb.elapsed().as_secs_f64() / done as f64
                );
            }
            if budget_hit(el()) {
                break;
            }
        }
        println!(
            "  level {minlev}: {done} of {} sets ({at_level} deficient at this level): {up} refuted (bound +1), {ex} exact, {to} timed out ({:.0}s)",
            batch.len(), el()
        );
    }
    // final pass over all 840^3 triples
    let lbt = lb_tables(&sets);
    let ex_t: Vec<Vec<bool>> = ids.iter().map(|tab| tab.iter().map(|&id| sets[id as usize].exact).collect()).collect();
    let rows: Vec<(usize, usize, Vec<String>, u16)> = (0..n)
        .into_par_iter()
        .map(|x| {
            let (mut bad, mut genuine, mut lines, mut lo) = (0usize, 0usize, Vec::new(), u16::MAX);
            for y in 0..n {
                let a = lbt[0][x * n + y] as u16;
                for z in 0..n {
                    let s = a + lbt[1][y * n + z] as u16 + lbt[2][z * n + x] as u16;
                    lo = lo.min(s);
                    if s < goal {
                        bad += 1;
                        let real = ex_t[0][x * n + y] && ex_t[1][y * n + z] && ex_t[2][z * n + x];
                        genuine += real as usize;
                        if lines.len() < 200 {
                            lines.push(format!(
                                "0 {:04x} {:04x} {:04x} {} {}",
                                reps[x].0, reps[y].0, reps[z].0, s as usize + r - NIN, if real { "exact" } else { "open" }
                            ));
                        }
                    }
                }
            }
            (bad, genuine, lines, lo)
        })
        .collect();
    let bad: usize = rows.iter().map(|t| t.0).sum();
    let genuine: usize = rows.iter().map(|t| t.1).sum();
    let lo = rows.iter().map(|t| t.3).min().unwrap() as usize;
    println!("orbit lower bound proved: every point costs at least {}", lo + r - NIN);
    let mut hist = vec![0usize; 64];
    for s in &sets {
        hist[s.lev as usize] += 1;
    }
    println!("helper levels refuted per set: {}", hist_str(&hist));
    if bad == 0 {
        println!("PROVED: every point of the orbit costs at least {} ({:.0}s)", o.target, el());
    } else {
        println!(
            "NOT PROVED: {bad} coset triples may cost less than {}: {genuine} with all three sides exact (genuine points), {} with an open side  ({:.0}s)",
            o.target, bad - genuine, el()
        );
        if let Some(dir) = &o.out {
            std::fs::create_dir_all(dir).unwrap();
            let txt: String = rows.iter().flat_map(|t| t.2.iter()).map(|l| format!("{l}\n")).collect();
            std::fs::write(format!("{dir}/lbscan_triples.txt"), txt).unwrap();
            let stuck: String = sets
                .iter()
                .filter(|s| s.stuck)
                .map(|s| format!("{} lb {} {}\n", s.key.iter().map(|v| format!("{v:04x}")).collect::<Vec<_>>().join(","), s.key.len() + s.lev as usize, s.key.len()))
                .collect();
            std::fs::write(format!("{dir}/lbscan_open_sides.txt"), stuck).unwrap();
            println!("wrote up to 200 triples per X to {dir}/lbscan_triples.txt and the open sides to {dir}/lbscan_open_sides.txt");
        }
    }
}

/// Cross-check lbscan's refutations with the older search (exact_dfs:
/// at most k helpers, pairwise order rule only, copied state): the deepest
/// non-exact sets of a checkpoint must have no program with lev-1 helpers,
/// and a sample of exact sets must have one with lev helpers.
fn lbcheck1(pre: &str, cache: &str, o: &Opts) {
    let s0 = Scheme::from_sms(pre);
    let reps = coset_reps(&gl42());
    let n = reps.len();
    let fams = [&s0.u, &s0.v, &s0.w];
    // rebuild the set numbering exactly as lbscan does
    let mut index: HashMap<Vec<u16>, u32> = HashMap::new();
    let mut keys: Vec<Vec<u16>> = Vec::new();
    for which in 0..3 {
        let ks: Vec<Vec<u16>> = (0..n * n)
            .into_par_iter()
            .map(|e| {
                let (xi, xj) = (reps[e / n], reps[e % n]);
                let mut t: Vec<u16> = fams[which]
                    .iter()
                    .map(|&m| if which < 2 { m_mul(m_mul(m_t(xi.0), m), m_t(xj.1)) } else { m_mul(m_mul(xj.1, m), xi.0) })
                    .filter(|v| v.count_ones() > 1)
                    .collect();
                t.sort_unstable();
                t.dedup();
                t
            })
            .collect();
        for t in ks {
            if !index.contains_key(&t) {
                index.insert(t.clone(), keys.len() as u32);
                keys.push(t);
            }
        }
    }
    let khash = |k: &[u16]| k.iter().fold(0xcbf2_9ce4_8422_2325u64 ^ k.len() as u64, |h, &v| (h ^ v as u64).wrapping_mul(0x0000_0100_0000_01b3));
    let mut st: HashMap<usize, (u8, bool)> = HashMap::new();
    for ln in std::fs::read_to_string(cache).unwrap().lines() {
        let f: Vec<&str> = ln.split_whitespace().collect();
        let (id, h, lev, ex): (usize, u64, u8, bool) = (f[0].parse().unwrap(), u64::from_str_radix(f[1], 16).unwrap(), f[2].parse().unwrap(), f[3] == "1");
        assert!(id < keys.len() && khash(&keys[id]) == h, "checkpoint does not match this scheme");
        let e = st.entry(id).or_insert((0, false));
        e.0 = e.0.max(lev);
        e.1 |= ex;
    }
    // a seeded sample at exactly level --depth (refuted) and --depth - 1 (exact)
    let mut rng = Rng(o.seed ^ 0x5eed);
    let mut sample = |want_exact: bool, lev: usize, k: usize| -> Vec<(usize, u8)> {
        let mut v: Vec<(usize, u8)> = st.iter().filter(|(_, x)| x.1 == want_exact && x.0 as usize == lev).map(|(&i, x)| (i, x.0)).collect();
        v.sort();
        for a in (1..v.len()).rev() {
            v.swap(a, rng.below(a + 1));
        }
        v.truncate(k);
        v
    };
    let refuted = sample(false, o.depth, o.maxsub);
    let exact = sample(true, o.depth.saturating_sub(1), o.maxsub / 4 + 1);
    println!("{} sets in checkpoint; re-checking {} refutations at level {} and {} exact sets at level {}", st.len(), refuted.len(), o.depth, exact.len(), o.depth.saturating_sub(1));
    let run = |key: &[u16], k: usize| -> Option<bool> {
        DEADLINE.with(|d| d.set(Some(std::time::Instant::now() + std::time::Duration::from_secs_f64(o.cap))));
        TIMED_OUT.with(|f| f.set(false));
        let mut inc = vec![0u64; NV / 64];
        let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
        for &c in &cl {
            bput(&mut inc, c);
        }
        let mut rem = key.to_vec();
        closure(&mut inc, &mut cl, &mut rem);
        let nodes = std::sync::atomic::AtomicU64::new(0);
        let r = exact_dfs(&inc, &cl, &rem, k, None, &nodes);
        let to = TIMED_OUT.with(|f| f.get());
        DEADLINE.with(|d| d.set(None));
        if r.is_some() { Some(true) } else if to { None } else { Some(false) }
    };
    let t0 = std::time::Instant::now();
    let a: Vec<(usize, u8, Option<bool>)> = refuted.par_iter().map(|&(i, l)| (i, l, run(&keys[i], l as usize - 1))).collect();
    let b: Vec<(usize, u8, Option<bool>)> = exact.par_iter().map(|&(i, l)| (i, l, run(&keys[i], l as usize))).collect();
    let cnt = |v: &[(usize, u8, Option<bool>)], w: Option<bool>| v.iter().filter(|t| t.2 == w).count();
    println!(
        "refutations: {} confirmed, {} CONTRADICTED, {} timed out; exact: {} confirmed, {} CONTRADICTED, {} timed out  ({:.0}s)",
        cnt(&a, Some(false)), cnt(&a, Some(true)), cnt(&a, None), cnt(&b, Some(true)), cnt(&b, Some(false)), cnt(&b, None),
        t0.elapsed().as_secs_f64()
    );
    let mut hist: std::collections::BTreeMap<u8, (usize, usize)> = std::collections::BTreeMap::new();
    for t in &a {
        let e = hist.entry(t.1).or_default();
        e.0 += 1;
        e.1 += (t.2 == Some(false)) as usize;
    }
    println!("refutations re-checked by level (lev: checked, confirmed): {:?}", hist);
    for t in a.iter().filter(|t| t.2 == Some(true)) {
        println!("CONTRADICTION: set {} ({} targets) lev {}", t.0, keys[t.0].len(), t.1);
    }
}

/// Settle the open sides of refined orbit points (a `refine` log): for each
/// distinct open side (target set), search exactly one helper below the
/// BP count, and lower while found; then recompute every point's total.
fn settle(pre: &str, logf: &str, o: &Opts) {
    let s0 = Scheme::from_sms(pre);
    assert!(s0.brent_ok(), "input scheme fails Brent");
    let g = gl42();
    let inv: HashMap<u16, u16> = g.iter().copied().collect();
    let r = s0.u.len();
    // parse "point S X Y Z (quick Q): L tok R tok Pt tok -> total T"
    struct Pt { sg: usize, x: u16, y: u16, z: u16, toks: [(usize, usize); 3] }
    let mut pts = Vec::new();
    for ln in std::fs::read_to_string(logf).unwrap().lines() {
        if !ln.starts_with("point ") {
            continue;
        }
        let f: Vec<&str> = ln.split_whitespace().collect();
        let sg: usize = f[1].parse().unwrap();
        let (x, y, z) = (u16::from_str_radix(f[2], 16).unwrap(), u16::from_str_radix(f[3], 16).unwrap(), u16::from_str_radix(f[4], 16).unwrap());
        let tok = |s: &str| -> (usize, usize) {
            // "44=" "49!" "50?49" -> (lb, ub)
            let cut = s.find(|c: char| !c.is_ascii_digit()).unwrap();
            let ub: usize = s[..cut].parse().unwrap();
            if &s[cut..cut + 1] == "?" { (s[cut + 1..].parse().unwrap(), ub) } else { (ub, ub) }
        };
        let li = f.iter().position(|&w| w == "L").unwrap();
        pts.push(Pt { sg, x, y, z, toks: [tok(f[li + 1]), tok(f[li + 3]), tok(f[li + 5])] });
    }
    let best0 = pts.iter().map(|p| p.toks.iter().map(|t| t.1).sum::<usize>() + r - NIN).min().unwrap();
    // only points that could reach below `goal` matter
    let goal = if o.target > 0 { o.target } else { best0 };
    let outdir = o.out.clone().unwrap_or_else(|| ".".into());
    std::fs::create_dir_all(&outdir).unwrap();
    let cache_path = format!("{outdir}/settled_sides.txt");
    let key_str = |k: &Vec<u16>| k.iter().map(|v| format!("{v:04x}")).collect::<Vec<_>>().join(",");
    let mut cached: HashMap<String, (usize, usize)> = HashMap::new();
    if let Ok(txt) = std::fs::read_to_string(&cache_path) {
        for ln in txt.lines() {
            let f: Vec<&str> = ln.split_whitespace().collect();
            if f.len() == 3 {
                cached.insert(f[0].to_string(), (f[1].parse().unwrap(), f[2].parse().unwrap()));
            }
        }
    }
    let syms: Vec<Scheme> = (0..6).map(|i| s0.sym(i)).collect();
    // collect open sides: (sorted target set, raw rows, BP ub, lb)
    let mut sides: HashMap<Vec<u16>, (Vec<u16>, usize, usize)> = HashMap::new();
    let mut point_sides: Vec<[Vec<u16>; 3]> = Vec::new();
    for p in &pts {
        let s = syms[p.sg].act((p.x, inv[&p.x]), (p.y, inv[&p.y]), (p.z, inv[&p.z]));
        let lbsum: usize = p.toks.iter().map(|t| t.0).sum::<usize>() + r - NIN;
        let mut keys: [Vec<u16>; 3] = Default::default();
        for (k, m) in [&s.u, &s.v, &s.w].into_iter().enumerate() {
            let mut ts: Vec<u16> = m.iter().copied().filter(|v| v.count_ones() > 1).collect();
            ts.sort_unstable();
            ts.dedup();
            keys[k] = ts.clone();
            let (lb, ub) = p.toks[k];
            if lb < ub && lbsum < goal {
                let e = sides.entry(ts).or_insert((m.clone(), ub, lb));
                e.1 = e.1.min(ub);
                e.2 = e.2.max(lb);
            }
        }
        point_sides.push(keys);
    }
    let mut work: Vec<(usize, Vec<u16>)> = sides
        .iter()
        .map(|(k, v)| (v.1 - 1 - k.len(), k.clone()))
        .filter(|(h, _)| *h <= o.depth)
        .collect();
    work.sort();
    println!("{} points (best {best0}); {} open sides, {} within {} helpers", pts.len(), sides.len(), work.len(), o.depth);
    // exact results per side key: (exact value or improved ub, proved lb)
    let mut res: HashMap<Vec<u16>, (usize, usize)> = HashMap::new();
    let t0 = std::time::Instant::now();
    for (i, (h, key)) in work.iter().enumerate() {
        let (_rows, ub, _lb) = sides[key].clone();
        if let Some(&(cu, cl_)) = cached.get(&key_str(key)) {
            res.insert(key.clone(), (cu, cl_));
            println!("side {}/{}: {} targets, BP {} -> {} (lb {}) [cached]", i + 1, work.len(), key.len(), ub, cu, cl_);
            continue;
        }
        let mut inc = vec![0u64; NV / 64];
        let mut cl: Vec<u16> = (0..NIN).map(|i| 1u16 << i).collect();
        for &c in &cl {
            bput(&mut inc, c);
        }
        let mut rem = key.clone();
        closure(&mut inc, &mut cl, &mut rem);
        let mut cur_ub = ub;
        let mut proved_lb = None;
        let mut hh = *h;
        loop {
            GLOBAL_TIMED_OUT.store(false, std::sync::atomic::Ordering::Relaxed);
            GLOBAL_DEADLINE_MS.store(epoch_ms() + (o.cap * 1000.0) as u64, std::sync::atomic::Ordering::Relaxed);
            let nodes = std::sync::atomic::AtomicU64::new(0);
            let found = exact_level(&inc, &cl, &rem, hh, true, &nodes);
            GLOBAL_DEADLINE_MS.store(0, std::sync::atomic::Ordering::Relaxed);
            let to = GLOBAL_TIMED_OUT.load(std::sync::atomic::Ordering::Relaxed);
            match found {
                Some(hs) => {
                    cur_ub = key.len() + hs.len();
                    if hs.is_empty() || hh == 0 {
                        proved_lb = Some(cur_ub);
                        break;
                    }
                    hh = hs.len() - 1;
                }
                None if to => break,
                None => {
                    proved_lb = Some(key.len() + hh + 1);
                    break;
                }
            }
        }
        let lb = proved_lb.unwrap_or(sides[key].2);
        res.insert(key.clone(), (cur_ub, lb));
        {
            use std::io::Write;
            let mut f = std::fs::OpenOptions::new().create(true).append(true).open(&cache_path).unwrap();
            writeln!(f, "{} {} {}", key_str(key), cur_ub, lb).unwrap();
        }
        println!(
            "side {}/{}: {} targets, BP {} -> {}{}  ({:.0}s)",
            i + 1, work.len(), key.len(), ub, cur_ub,
            if proved_lb == Some(cur_ub) { " exact".to_string() } else { format!(" (lb {lb})") },
            t0.elapsed().as_secs_f64()
        );
    }
    // recompute totals
    let mut totals: Vec<(usize, usize, usize)> = Vec::new(); // (ub, lb, point index)
    for (pi, p) in pts.iter().enumerate() {
        let (mut ub, mut lb) = (r - NIN, r - NIN);
        for k in 0..3 {
            let (l0, u0) = p.toks[k];
            match res.get(&point_sides[pi][k]) {
                Some(&(u, l)) => { ub += u.min(u0); lb += l.max(l0); }
                None => { ub += u0; lb += l0; }
            }
        }
        totals.push((ub, lb, pi));
    }
    totals.sort();
    let best = totals[0].0;
    let open = totals.iter().filter(|t| t.1 < best).count();
    // dump points that could still go below `goal`, with each side's status
    let mut dump = String::new();
    for &(ub, lb, pi) in &totals {
        if lb >= goal {
            continue;
        }
        let p = &pts[pi];
        dump += &format!("point {} {:04x} {:04x} {:04x} total {ub} lb {lb}:", p.sg, p.x, p.y, p.z);
        for k in 0..3 {
            let (l0, u0) = p.toks[k];
            let (u, l) = match res.get(&point_sides[pi][k]) {
                Some(&(u, l)) => (u.min(u0), l.max(l0)),
                None => (u0, l0),
            };
            dump += &format!(" [{} targets, ub {u}, lb {l}, need {}]", point_sides[pi][k].len(), u.saturating_sub(1).saturating_sub(point_sides[pi][k].len()));
        }
        dump += "\n";
    }
    std::fs::write(format!("{outdir}/settle_open.txt"), dump).unwrap();
    println!("best total {best}; points still open below it: {open}");
    for &(ub, lb, pi) in totals.iter().take(8) {
        let p = &pts[pi];
        println!("  point {} {:04x} {:04x} {:04x}: total {ub} (lb {lb})", p.sg, p.x, p.y, p.z);
    }
    if best < best0 {
        println!("IMPROVED: {best} < {best0} -- rerun `refine` on the point above to emit and verify its programs");
    }
}

fn binom(n: usize, k: usize) -> f64 {
    (0..k).fold(1.0, |acc, i| acc * (n - i) as f64 / (i + 1) as f64)
}

fn combos(n: usize, k: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut c: Vec<usize> = (0..k).collect();
    if k > n {
        return out;
    }
    loop {
        out.push(c.clone());
        let mut i = k;
        loop {
            if i == 0 {
                return out;
            }
            i -= 1;
            if c[i] != i + n - k {
                break;
            }
            if i == 0 && c[0] == n - k {
                return out;
            }
        }
        c[i] += 1;
        for j in (i + 1)..k {
            c[j] = c[j - 1] + 1;
        }
    }
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
        let mut oo = OrbitOpts { restarts: 24, sweeps: 6, topk: 200, final_runs: 64, anneal: 0, t0: 2.0, t1: 0.2, collect: 0 };
        let mut i = 3;
        while i < args.len() {
            match args[i].as_str() {
                "--restarts" => { oo.restarts = args[i + 1].parse().unwrap(); i += 2; }
                "--sweeps" => { oo.sweeps = args[i + 1].parse().unwrap(); i += 2; }
                "--topk" => { oo.topk = args[i + 1].parse().unwrap(); i += 2; }
                "--final-runs" => { oo.final_runs = args[i + 1].parse().unwrap(); i += 2; }
                "--anneal" => { oo.anneal = args[i + 1].parse().unwrap(); i += 2; }
                "--t0" => { oo.t0 = args[i + 1].parse().unwrap(); i += 2; }
                "--t1" => { oo.t1 = args[i + 1].parse().unwrap(); i += 2; }
                "--collect" => { oo.collect = args[i + 1].parse().unwrap(); i += 2; }
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
    if args[1] == "scan" {
        // xor47 scan PREFIX [--runs BP_PER_ENTRY] [--depth SLACK] [--threads T] [--out DIR]
        let o = parse_opts(&args[3..]);
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
        let t0 = std::time::Instant::now();
        scan(&args[2], &o);
        println!("({:.1}s)", t0.elapsed().as_secs_f64());
        return;
    }
    if args[1] == "screen" {
        // xor47 screen LIST --runs STEPS --depth CHAINS [--threads T] [--out RANKED.txt]
        let o = parse_opts(&args[3..]);
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
        let t0 = std::time::Instant::now();
        screen(&args[2], &o, o.runs, o.depth.max(1));
        println!("({:.1}s)", t0.elapsed().as_secs_f64());
        return;
    }
    if args[1] == "lbcheck1" {
        // xor47 lbcheck1 PREFIX CHECKPOINT [--depth LEV] [--maxsub N] [--cap SECS] [--threads T]
        let o = parse_opts(&args[4..]);
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
        lbcheck1(&args[2], &args[3], &o);
        return;
    }
    if args[1] == "lbscan" {
        // xor47 lbscan PREFIX --target T [--depth HMAX] [--cap SECS] [--threads T] [--out DIR]
        let o = parse_opts(&args[3..]);
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
        let t0 = std::time::Instant::now();
        lbscan(&args[2], &o);
        println!("({:.1}s)", t0.elapsed().as_secs_f64());
        return;
    }
    if args[1] == "settle" {
        // xor47 settle PREFIX REFINE_LOG [--depth HMAX] [--cap SECS] [--threads T]
        let o = parse_opts(&args[4..]);
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
        let t0 = std::time::Instant::now();
        settle(&args[2], &args[3], &o);
        println!("({:.1}s)", t0.elapsed().as_secs_f64());
        return;
    }
    if args[1] == "refine" {
        // xor47 refine PREFIX CANDS [--runs BPRUNS] [--cap SECS] [--threads T] [--out DIR]
        let o = parse_opts(&args[4..]);
        rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
        let t0 = std::time::Instant::now();
        refine(&args[2], &args[3], &o);
        println!("({:.1}s)", t0.elapsed().as_secs_f64());
        return;
    }
    let o = parse_opts(&args[3..]);
    rayon::ThreadPoolBuilder::new().num_threads(o.threads).build_global().unwrap();
    let t0 = std::time::Instant::now();
    match args[1].as_str() {
        "lns" => {
            // xor47 lns M.sms [--transpose] [--runs POOL] [--depth D] [--maxsub S] [--out M.slp]
            let (rows, cols, m) = read_sms(&args[2]);
            let targets: Vec<u16> = if o.transpose {
                transpose(rows, cols, &m).iter().map(|&v| v as u16).collect()
            } else {
                m.iter().map(|&v| v as u16).collect()
            };
            match lns(&targets, &o, o.depth, o.maxsub) {
                Some(p) => {
                    verify(&p, &targets);
                    let (txt, x) = if o.transpose { emit_transposed(&p, &targets) } else { emit_direct(&p, &targets) };
                    println!("{}: IMPROVED to {} XORs ({x} as emitted)", args[2], p.xors());
                    if let Some(f) = &o.out {
                        std::fs::write(f, txt).unwrap();
                    }
                }
                None => println!("{}: no improvement found", args[2]),
            }
            println!("({:.1}s)", t0.elapsed().as_secs_f64());
        }
        "exact" => {
            // xor47 exact M.sms [--transpose] --runs HMAX  (HMAX helpers at most)
            let (rows, cols, m) = read_sms(&args[2]);
            let targets: Vec<u16> = if o.transpose {
                transpose(rows, cols, &m).iter().map(|&v| v as u16).collect()
            } else {
                m.iter().map(|&v| v as u16).collect()
            };
            match exact(&targets, o.runs) {
                Some((c, hs)) => {
                    println!("{}: exact minimum {c} XORs, helpers {:04x?}", args[2], hs);
                    let p = replay(&targets, &[], &hs).expect("exact helpers must replay");
                    verify(&p, &targets);
                    assert_eq!(p.xors(), c, "replayed program size differs");
                    let (txt, x) = if o.transpose { emit_transposed(&p, &targets) } else { emit_direct(&p, &targets) };
                    println!("  program: {} XORs ({x} as emitted)", p.xors());
                    if let Some(f) = &o.out {
                        std::fs::write(f, txt).unwrap();
                    }
                }
                None => println!("{}: more than (targets + {}) XORs needed", args[2], o.runs),
            }
            println!("({:.1}s)", t0.elapsed().as_secs_f64());
        }
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
