//! bench315r — recursive rank-48 vs naive witness generation over
//! Goldilocks: locate the crossover size. The generated SLPs
//! (slp315g.rs) are generic over El, so the same 315-op linear
//! phases run on scalars and on (n/4)x(n/4) blocks; recursion uses
//! rank-48 block structure down to a cutoff tile, then naive tiles.
//! Correctness gate at every size (vs plain naive).
const P: u64 = 0xFFFF_FFFF_0000_0001;

#[inline(always)]
fn fmul(a: u64, b: u64) -> u64 {
    ((a as u128 * b as u128) % (P as u128)) as u64
}
#[inline(always)]
fn fadd(a: u64, b: u64) -> u64 {
    let (s, c) = a.overflowing_add(b);
    let mut r = s;
    if c || r >= P {
        r = r.wrapping_sub(P);
    }
    r
}
#[inline(always)]
fn fsub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a.wrapping_sub(b).wrapping_add(P) }
}
#[inline(always)]
fn fneg_s(a: u64) -> u64 {
    if a == 0 { 0 } else { P - a }
}

fn pow2c(k: i32) -> u64 {
    // 2^k mod P for k in -4..=4
    let inv2 = (P + 1) / 2;
    let mut v = 1u64;
    if k >= 0 {
        for _ in 0..k {
            v = fadd(v, v);
        }
    } else {
        for _ in 0..(-k) {
            v = fmul(v, inv2);
        }
    }
    v
}

pub trait El: Clone {
    fn add(&self, o: &Self) -> Self;
    fn sub(&self, o: &Self) -> Self;
    fn neg(&self) -> Self;
    fn scale2(&self, k: i32) -> Self;
}

impl El for u64 {
    fn add(&self, o: &Self) -> Self {
        fadd(*self, *o)
    }
    fn sub(&self, o: &Self) -> Self {
        fsub(*self, *o)
    }
    fn neg(&self) -> Self {
        fneg_s(*self)
    }
    fn scale2(&self, k: i32) -> Self {
        fmul(*self, pow2c(k))
    }
}

#[derive(Clone)]
pub struct Blk(Vec<u64>);

impl El for Blk {
    fn add(&self, o: &Self) -> Self {
        Blk(self.0.iter().zip(&o.0).map(|(a, b)| fadd(*a, *b)).collect())
    }
    fn sub(&self, o: &Self) -> Self {
        Blk(self.0.iter().zip(&o.0).map(|(a, b)| fsub(*a, *b)).collect())
    }
    fn neg(&self) -> Self {
        Blk(self.0.iter().map(|a| fneg_s(*a)).collect())
    }
    fn scale2(&self, k: i32) -> Self {
        let c = pow2c(k);
        Blk(self.0.iter().map(|a| fmul(*a, c)).collect())
    }
}

include!("../slp315g.rs");

fn naive_n(n: usize, a: &[u64], b: &[u64], c: &mut [u64]) {
    for i in 0..n {
        for j in 0..n {
            let mut s = 0u64;
            for k in 0..n {
                s = fadd(s, fmul(a[i * n + k], b[k * n + j]));
            }
            c[i * n + j] = s;
        }
    }
}

/// recursive rank-48: blocks of size n/4, cutoff -> naive tiles
fn fast_n(n: usize, cutoff: usize, a: &[u64], b: &[u64], c: &mut [u64]) {
    if n <= cutoff {
        naive_n(n, a, b, c);
        return;
    }
    let h = n / 4;
    let grab = |m: &[u64], bi: usize, bj: usize| -> Blk {
        let mut v = Vec::with_capacity(h * h);
        for i in 0..h {
            let row = (bi * h + i) * n + bj * h;
            v.extend_from_slice(&m[row..row + h]);
        }
        Blk(v)
    };
    let ab: Vec<Blk> = (0..16).map(|x| grab(a, x / 4, x % 4)).collect();
    let bb: Vec<Blk> = (0..16).map(|y| grab(b, y / 4, y % 4)).collect();
    let zero = Blk(vec![0u64; h * h]);
    let mut la: Vec<Blk> = vec![zero.clone(); 48];
    let mut rb: Vec<Blk> = vec![zero.clone(); 48];
    gslp_l(&ab, &mut la);
    gslp_r(&bb, &mut rb);
    let mut pr: Vec<Blk> = Vec::with_capacity(48);
    for t in 0..48 {
        let mut out = vec![0u64; h * h];
        fast_n(h, cutoff, &la[t].0, &rb[t].0, &mut out);
        pr.push(Blk(out));
    }
    let mut co: Vec<Blk> = vec![zero; 16];
    gslp_p(&pr, &mut co);
    for z in 0..16 {
        let (zi, zj) = (z / 4, z % 4);
        for i in 0..h {
            let row = (zi * h + i) * n + zj * h;
            c[row..row + h].copy_from_slice(&co[z].0[i * h..(i + 1) * h]);
        }
    }
}

fn main() {
    let mut rng = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng % P
    };
    // correctness gate at n=16, 64
    for &n in &[16usize, 64] {
        let a: Vec<u64> = (0..n * n).map(|_| next()).collect();
        let b: Vec<u64> = (0..n * n).map(|_| next()).collect();
        let mut c1 = vec![0u64; n * n];
        let mut c2 = vec![0u64; n * n];
        naive_n(n, &a, &b, &mut c1);
        fast_n(n, 4, &a, &b, &mut c2);
        assert_eq!(c1, c2, "recursive mismatch at n={n}");
    }
    println!("field-verified: recursive rank-48 == naive at n=16, 64");

    for &n in &[16usize, 64, 256, 1024] {
        let a: Vec<u64> = (0..n * n).map(|_| next()).collect();
        let b: Vec<u64> = (0..n * n).map(|_| next()).collect();
        let mut c = vec![0u64; n * n];
        let reps = (200_000_000usize / (n * n * n)).max(1);
        let t0 = std::time::Instant::now();
        for _ in 0..reps {
            naive_n(n, &a, &b, &mut c);
        }
        let tn = t0.elapsed().as_secs_f64() / reps as f64;
        let mut best = (f64::MAX, 0usize);
        for &cut in &[4usize, 16, 64] {
            if cut >= n {
                continue;
            }
            let t1 = std::time::Instant::now();
            for _ in 0..reps {
                fast_n(n, cut, &a, &b, &mut c);
            }
            let tf = t1.elapsed().as_secs_f64() / reps as f64;
            if tf < best.0 {
                best = (tf, cut);
            }
        }
        println!(
            "n={n:5}  naive {:>10.3} ms   rank48-recursive {:>10.3} ms (cutoff {})   ratio {:.2}",
            tn * 1e3,
            best.0 * 1e3,
            best.1,
            best.0 / tn
        );
    }
}
