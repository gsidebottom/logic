//! kres: candidates for a k-subset re-solve of an F2 matrix-multiplication scheme.
//!
//! Drop k products of a scheme and ask whether their sum R (a tensor of rank at most k)
//! can be rewritten with k-1 products (a scheme of rank r-1) or with k different ones
//! (another scheme of rank r, possibly in a new equivalence class).  The rank of R is at
//! least each of its three flattening ranks; the c-flattening has rank k unless the k
//! c-factors are dependent or the k Kronecker products a_t (x) b_t are dependent (the
//! image of the flattening is U_ab applied to the row space of C), and likewise for a and
//! b.  So a rewrite with k-1 products needs, in every slot, dependent factors or
//! dependent Kronecker products of the other two slots ("R" candidates).  By Kruskal's
//! theorem a k-term decomposition whose factor matrices have Kruskal ranks summing to at
//! least 2k+2 is unique; for a scheme without repeated factors that holds as soon as two
//! slots are independent, so an alternative needs dependent factors in at least two slots
//! ("A" candidates).
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
type Wide = [u64; 4]; // a Kronecker product of two 16-bit factors, 256 bits

fn kron(x: u32, y: u32, wy: usize) -> Wide {
    // bit i*wy + j = x_i y_j
    let mut w: Wide = [0; 4];
    for i in 0..32 {
        if (x >> i) & 1 == 1 {
            let base = i * wy;
            for j in 0..wy {
                if (y >> j) & 1 == 1 {
                    let b = base + j;
                    w[b / 64] |= 1u64 << (b % 64);
                }
            }
        }
    }
    w
}

fn wide_lead(w: &Wide) -> i32 {
    for q in (0..4).rev() {
        if w[q] != 0 { return (q as i32) * 64 + 63 - w[q].leading_zeros() as i32; }
    }
    -1
}

#[derive(Clone)]
struct WBasis { v: Vec<Wide> } // echelon by leading bit, descending
impl WBasis {
    fn new() -> Self { WBasis { v: Vec::with_capacity(8) } }
    fn reduce(&self, mut x: Wide) -> Wide {
        for b in &self.v {
            let l = wide_lead(b);
            if l >= 0 && (x[(l / 64) as usize] >> (l % 64)) & 1 == 1 {
                for q in 0..4 { x[q] ^= b[q]; }
            }
        }
        x
    }
    fn insert(&mut self, x: Wide) {
        let l = wide_lead(&x);
        let pos = self.v.iter().position(|b| wide_lead(b) < l).unwrap_or(self.v.len());
        self.v.insert(pos, x);
    }
}

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
    krons: &'a [[Wide; 3]], // per product: a(x)b, a(x)c, b(x)c
    k: usize,
    both: bool,
    chosen: Vec<usize>,
    out: Vec<String>,
    visited: u64,
}

impl<'a> Walk<'a> {
    fn dfs(&mut self, start: usize, bases: &[Basis; 3], wb: &[WBasis; 3], dep: [bool; 3], kdep: [bool; 3]) {
        if self.chosen.len() == self.k {
            self.visited += 1;
            let ndep = dep.iter().filter(|&&d| d).count();
            // flattening rank of slot c drops when the c-factors or the a(x)b products are dependent, etc.
            let flat = [dep[0] || kdep[2], dep[1] || kdep[1], dep[2] || kdep[0]];
            let reducible = flat.iter().all(|&d| d);
            if reducible || (self.both && ndep >= 2) {
                let tag = if reducible { "R" } else { "A" };
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
            let mut nwb = wb.clone();
            let mut nkd = kdep;
            for s in 0..3 {
                let r = nwb[s].reduce(self.krons[i][s]);
                if r == [0; 4] { nkd[s] = true; } else { nwb[s].insert(r); }
            }
            self.chosen.push(i);
            self.dfs(i + 1, &nb, &nwb, nd, nkd);
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
    let (wb_, wc_) = (n2 * n3, n1 * n3);
    let krons: Vec<[Wide; 3]> = prods.iter().map(|p| [kron(p[0], p[1], wb_), kron(p[0], p[2], wc_), kron(p[1], p[2], wc_)]).collect();
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
                        let mut w = Walk { prods: &prods, krons: &krons, k, both, chosen: vec![i0], out: Vec::new(), visited: 0 };
                        let mut b = [Basis::new(), Basis::new(), Basis::new()];
                        for s in 0..3 { b[s].insert(prods[i0][s]); }
                        let mut wbs = [WBasis::new(), WBasis::new(), WBasis::new()];
                        for s in 0..3 { wbs[s].insert(krons[i0][s]); }
                        w.dfs(i0 + 1, &b, &wbs, [false; 3], [false; 3]);
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
        println!("c k={k}: {visited} subsets, {nr} reduction candidates (all three flattening ranks below k), {na} alternative candidates (two dependent slots), {:.1} s",
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
