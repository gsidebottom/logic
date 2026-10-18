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
    cap: f64,
    depth: usize,
    maxsub: usize,
    runs: usize,
    threads: usize,
    seed: u64,
    prm: Params,
    out: Option<String>,
    transpose: bool,
}

fn parse_opts(args: &[String]) -> Opts {
    let mut o = Opts {
        cap: 30.0,
        depth: 3,
        maxsub: 200,
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
            "--depth" => o.depth = val().parse().unwrap(),
            "--cap" => o.cap = val().parse().unwrap(),
            "--maxsub" => o.maxsub = val().parse().unwrap(),
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

fn past_deadline() -> bool {
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
        let found = if rem.is_empty() {
            Some(Vec::new())
        } else if h == 0 {
            None
        } else {
            exact_dfs(&inc, &cl, &rem, h, None, &nodes)
        };
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
        let found = if h == 0 {
            if rem.is_empty() { Some(Vec::new()) } else { None }
        } else {
            let ps = pairsums(&cl);
            let cands = helper_cands(&inc, &cl, &rem, &ps, h == 1);
            cands.par_iter().find_map_any(|&x| {
                let (mut inc2, mut cl2, mut rem2) = (inc.clone(), cl.clone(), rem.clone());
                bput(&mut inc2, x);
                cl2.push(x);
                closure(&mut inc2, &mut cl2, &mut rem2);
                if h == 1 && !rem2.is_empty() {
                    return None;
                }
                exact_dfs(&inc2, &cl2, &rem2, h - 1, Some((x, &ps)), &nodes).map(|mut hs| {
                    hs.insert(0, x);
                    hs
                })
            })
        };
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
