//! kres: candidates for a k-subset re-solve of an F2 matrix-multiplication scheme.
//!
//! Drop k products of a scheme and ask whether their sum R (a tensor of rank at most k)
//! can be rewritten with k-1 products (a scheme of rank r-1) or with k different ones
//! (another scheme of rank r, possibly in a new equivalence class).  Both need linear
//! dependencies among the dropped products' factors: the rank of R is at least each of
//! its three flattening ranks, which are the dimensions of the spans of the k a-factors,
//! b-factors and c-factors, so a rewrite with k-1 products needs all three spans of
//! dimension below k; and by Kruskal's theorem a k-term decomposition with two slots
//! independent is unique, so an alternative needs dependencies in at least two slots.
//! This tool enumerates every k-subset for k in kmin..=kmax and prints those with at
//! least two dependent slots ("A", alternative candidates) or three ("R", reduction
//! candidates), with the span dimensions; the exact questions are decided on the small
//! residual tensor by the SAT stage (matmul/tomar_line/proj/kres_solve.py).
//!
//! usage: kres N1 N2 N3 scheme.bits --kmin 3 --kmax 8 [--threads 12] [--out FILE]
//!        [--both]   (print A candidates too; default prints R candidates only)
//! bits layout: all a factors (n1*n2 bits each), then all b (n2*n3), then all c (n1*n3).
use std::io::Write;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Mutex;

type Prod = [u32; 3];

#[derive(Clone)]
struct Basis {
    v: Vec<u32>, // echelon: distinct leading bits, sorted by leading bit descending
}
impl Basis {
    fn new() -> Self { Basis { v: Vec::with_capacity(16) } }
    /// reduce x against the basis; a zero result means x is in the span
    fn reduce(&self, mut x: u32) -> u32 {
        for &b in &self.v {
            let lead = 31 - b.leading_zeros();
            if (x >> lead) & 1 == 1 { x ^= b; }
        }
        x
    }
    fn insert(&mut self, x: u32) {
        let lead = 31 - x.leading_zeros();
        let pos = self.v.iter().position(|&b| (31 - b.leading_zeros()) < lead).unwrap_or(self.v.len());
        self.v.insert(pos, x);
    }
    fn dim(&self) -> usize { self.v.len() }
}

fn arg_val<T: std::str::FromStr>(args: &[String], key: &str) -> Option<T> {
    args.iter().position(|a| a == key).and_then(|i| args.get(i + 1)).and_then(|s| s.parse().ok())
}

fn load(path: &str, n1: usize, n2: usize, n3: usize) -> Vec<Prod> {
    let txt = std::fs::read_to_string(path).expect("read scheme");
    let bits: Vec<u8> = txt.split_whitespace().last().unwrap().bytes().map(|b| b - b'0').collect();
    let (sa, sb, sg) = (n1 * n2, n2 * n3, n1 * n3);
    let per = sa + sb + sg;
    assert!(bits.len() % per == 0, "bits length {} not a multiple of {}", bits.len(), per);
    let r = bits.len() / per;
    let mut out = Vec::with_capacity(r);
    for m in 0..r {
        let mut p: Prod = [0, 0, 0];
        for k in 0..sa { p[0] |= (bits[m * sa + k] as u32) << k; }
        for k in 0..sb { p[1] |= (bits[r * sa + m * sb + k] as u32) << k; }
        for k in 0..sg { p[2] |= (bits[r * sa + r * sb + m * sg + k] as u32) << k; }
        out.push(p);
    }
    out
}

struct Walk<'a> {
    prods: &'a [Prod],
    k: usize,
    both: bool,
    chosen: Vec<usize>,
    out: Vec<String>,
    visited: u64,
}

impl<'a> Walk<'a> {
    fn dfs(&mut self, start: usize, bases: &[Basis; 3], dep: [bool; 3]) {
        if self.chosen.len() == self.k {
            self.visited += 1;
            let ndep = dep.iter().filter(|&&d| d).count();
            if ndep == 3 || (self.both && ndep == 2) {
                let tag = if ndep == 3 { "R" } else { "A" };
                let idx: Vec<String> = self.chosen.iter().map(|i| i.to_string()).collect();
                self.out.push(format!("{} k={} dims={},{},{} idx={}", tag, self.k, bases[0].dim(), bases[1].dim(), bases[2].dim(), idx.join(",")));
            }
            return;
        }
        let need = self.k - self.chosen.len();
        for i in start..=(self.prods.len() - need) {
            let mut nb = bases.clone();
            let mut nd = dep;
            for s in 0..3 {
                let r = nb[s].reduce(self.prods[i][s]);
                if r == 0 { nd[s] = true; } else { nb[s].insert(r); }
            }
            self.chosen.push(i);
            self.dfs(i + 1, &nb, nd);
            self.chosen.pop();
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.len() < 4 {
        eprintln!("usage: kres N1 N2 N3 scheme.bits --kmin K --kmax K [--threads T] [--out FILE] [--both]");
        std::process::exit(2);
    }
    let (n1, n2, n3): (usize, usize, usize) = (args[0].parse().unwrap(), args[1].parse().unwrap(), args[2].parse().unwrap());
    let prods = load(&args[3], n1, n2, n3);
    let kmin: usize = arg_val(&args, "--kmin").unwrap_or(3);
    let kmax: usize = arg_val(&args, "--kmax").unwrap_or(8);
    let threads: usize = arg_val(&args, "--threads").unwrap_or(12);
    let both = args.iter().any(|a| a == "--both");
    let out_path: Option<String> = arg_val(&args, "--out");
    let r = prods.len();
    // whole-scheme span dimensions, for the record
    let mut full = [Basis::new(), Basis::new(), Basis::new()];
    for p in &prods { for s in 0..3 { let x = full[s].reduce(p[s]); if x != 0 { full[s].insert(x); } } }
    println!("c kres: <{n1},{n2},{n3}> rank {r} from {}; factor span dims {},{},{}; k = {kmin}..{kmax}; {} candidates",
        args[3], full[0].dim(), full[1].dim(), full[2].dim(), if both { "R and A" } else { "R only" });
    let mut all: Vec<String> = Vec::new();
    for k in kmin..=kmax {
        let t0 = std::time::Instant::now();
        let next = AtomicUsize::new(0);
        let results: Mutex<Vec<(usize, Vec<String>, u64)>> = Mutex::new(Vec::new());
        std::thread::scope(|sc| {
            for _ in 0..threads {
                sc.spawn(|| {
                    loop {
                        let i0 = next.fetch_add(1, Ordering::Relaxed);
                        if i0 + k > r { break; }
                        let mut w = Walk { prods: &prods, k, both, chosen: vec![i0], out: Vec::new(), visited: 0 };
                        let mut b = [Basis::new(), Basis::new(), Basis::new()];
                        for s in 0..3 { b[s].insert(prods[i0][s]); }
                        w.dfs(i0 + 1, &b, [false; 3]);
                        results.lock().unwrap().push((i0, w.out, w.visited));
                    }
                });
            }
        });
        let mut res = results.into_inner().unwrap();
        res.sort_by_key(|x| x.0);
        let visited: u64 = res.iter().map(|x| x.2).sum();
        let mut lines: Vec<String> = res.into_iter().flat_map(|x| x.1).collect();
        let nr = lines.iter().filter(|l| l.starts_with('R')).count();
        let na = lines.len() - nr;
        println!("c k={k}: {visited} subsets, {nr} reduction candidates (3 dependent slots), {na} alternative candidates (2), {:.1} s",
            t0.elapsed().as_secs_f64());
        all.append(&mut lines);
    }
    if let Some(p) = out_path {
        let mut f = std::fs::File::create(&p).unwrap();
        for l in &all { writeln!(f, "{l}").unwrap(); }
        println!("c wrote {} candidates to {p}", all.len());
    } else {
        for l in &all { println!("{l}"); }
    }
}
