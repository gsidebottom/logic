//! bench_bbr — BabyBear recursion bench: locate the rank-48
//! witness-generation crossover over a 31-bit Montgomery field
//! (methodology matched to bench315r/bench284r over Goldilocks:
//! scalar arithmetic, same cutoff sweep, cache-blocked naive
//! control, correctness gates at every size). The El-generic 284
//! networks (slp284g.rs) run on u32 scalars and on (n/4)x(n/4)
//! blocks unchanged.
const P: u32 = 0x7800_0001;
const P64: u64 = P as u64;

const fn np_const() -> u32 {
    let mut inv: u32 = 1;
    let mut i = 0;
    while i < 5 {
        inv = inv.wrapping_mul(2u32.wrapping_sub(P.wrapping_mul(inv)));
        i += 1;
    }
    inv.wrapping_neg()
}
const NP: u32 = np_const();
const R2: u32 = ((1u128 << 64) % P as u128) as u32;

#[inline(always)]
fn mmul(a: u32, b: u32) -> u32 {
    let t = a as u64 * b as u64;
    let m = (t as u32).wrapping_mul(NP);
    let t2 = ((t + m as u64 * P64) >> 32) as u32;
    if t2 >= P { t2 - P } else { t2 }
}
#[inline(always)]
fn badd(a: u32, b: u32) -> u32 {
    let s = a + b;
    if s >= P { s - P } else { s }
}
#[inline(always)]
fn bsub(a: u32, b: u32) -> u32 {
    if a >= b { a - b } else { a + P - b }
}
#[inline(always)]
fn bneg(a: u32) -> u32 {
    if a == 0 { 0 } else { P - a }
}
fn mpow(mut b: u32, mut e: u64) -> u32 {
    let mut r = mmul(R2, 1); // to_m(1)
    while e > 0 {
        if e & 1 == 1 {
            r = mmul(r, b);
        }
        b = mmul(b, b);
        e >>= 1;
    }
    r
}
// Montgomery-form (1/2)^k constants, computed once
static INV2M: std::sync::OnceLock<[u32; 5]> = std::sync::OnceLock::new();

pub trait El: Clone {
    fn add(&self, o: &Self) -> Self;
    fn sub(&self, o: &Self) -> Self;
    fn neg(&self) -> Self;
    fn scale2(&self, k: i32) -> Self;
}

impl El for u32 {
    fn add(&self, o: &Self) -> Self {
        badd(*self, *o)
    }
    fn sub(&self, o: &Self) -> Self {
        bsub(*self, *o)
    }
    fn neg(&self) -> Self {
        bneg(*self)
    }
    fn scale2(&self, k: i32) -> Self {
        if k >= 0 {
            let mut v = *self;
            for _ in 0..k {
                v = badd(v, v);
            }
            v
        } else {
            mmul(*self, INV2M.get().unwrap()[(-k) as usize])
        }
    }
}

#[derive(Clone)]
pub struct Blk(Vec<u32>);
impl El for Blk {
    fn add(&self, o: &Self) -> Self {
        Blk(self.0.iter().zip(&o.0).map(|(a, b)| badd(*a, *b)).collect())
    }
    fn sub(&self, o: &Self) -> Self {
        Blk(self.0.iter().zip(&o.0).map(|(a, b)| bsub(*a, *b)).collect())
    }
    fn neg(&self) -> Self {
        Blk(self.0.iter().map(|a| bneg(*a)).collect())
    }
    fn scale2(&self, k: i32) -> Self {
        if k >= 0 {
            let mut v = self.0.clone();
            for _ in 0..k {
                for e in v.iter_mut() {
                    *e = badd(*e, *e);
                }
            }
            Blk(v)
        } else {
            let c = INV2M.get().unwrap()[(-k) as usize];
            Blk(self.0.iter().map(|a| mmul(*a, c)).collect())
        }
    }
}

include!("../slp284g.rs");

fn naive_blocked(n: usize, a: &[u32], b: &[u32], c: &mut [u32]) {
    const T: usize = 64;
    for x in c.iter_mut() {
        *x = 0;
    }
    let bs = T.min(n);
    for ii in (0..n).step_by(bs) {
        for kk in (0..n).step_by(bs) {
            for jj in (0..n).step_by(bs) {
                for i in ii..(ii + bs).min(n) {
                    for k in kk..(kk + bs).min(n) {
                        let av = a[i * n + k];
                        if av == 0 {
                            continue;
                        }
                        for j in jj..(jj + bs).min(n) {
                            c[i * n + j] = badd(c[i * n + j], mmul(av, b[k * n + j]));
                        }
                    }
                }
            }
        }
    }
}

fn naive_n(n: usize, a: &[u32], b: &[u32], c: &mut [u32]) {
    for i in 0..n {
        for j in 0..n {
            let mut s = 0u32;
            for k in 0..n {
                s = badd(s, mmul(a[i * n + k], b[k * n + j]));
            }
            c[i * n + j] = s;
        }
    }
}

fn fast_n(n: usize, cutoff: usize, a: &[u32], b: &[u32], c: &mut [u32]) {
    if n <= cutoff {
        naive_n(n, a, b, c);
        return;
    }
    let h = n / 4;
    let grab = |m: &[u32], bi: usize, bj: usize| -> Blk {
        let mut v = Vec::with_capacity(h * h);
        for i in 0..h {
            let row = (bi * h + i) * n + bj * h;
            v.extend_from_slice(&m[row..row + h]);
        }
        Blk(v)
    };
    let ab: Vec<Blk> = (0..16).map(|x| grab(a, x / 4, x % 4)).collect();
    let bb: Vec<Blk> = (0..16).map(|y| grab(b, y / 4, y % 4)).collect();
    let zero = Blk(vec![0u32; h * h]);
    let mut la: Vec<Blk> = vec![zero.clone(); 48];
    let mut rb: Vec<Blk> = vec![zero.clone(); 48];
    gslp_l(&ab, &mut la);
    gslp_r(&bb, &mut rb);
    let mut pr: Vec<Blk> = Vec::with_capacity(48);
    for t in 0..48 {
        let mut out = vec![0u32; h * h];
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
    assert_eq!(P.wrapping_mul(NP), u32::MAX, "np const");
    // gate Montgomery vs reference
    {
        let mut r = 0xdead_beefu64;
        let to_m = |x: u32| mmul(x, R2);
        let from_m = |x: u32| mmul(x, 1);
        for _ in 0..1_000_000 {
            r ^= r << 13;
            r ^= r >> 7;
            r ^= r << 17;
            let a = (r % P64) as u32;
            let b = (r.rotate_left(17) % P64) as u32;
            assert_eq!(
                from_m(mmul(to_m(a), to_m(b))) as u64,
                a as u64 * b as u64 % P64
            );
        }
        println!("Montgomery mul gated against reference on 1M randoms");
    }
    let inv2 = mpow(mmul(R2, 2), P64 - 2); // to_m(2)^-1 in mont form
    let mut inv2m = [0u32; 5];
    for (k, slot) in inv2m.iter_mut().enumerate() {
        *slot = mpow(inv2, k as u64);
    }
    INV2M.set(inv2m).unwrap();

    let mut rng = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        (rng % P64) as u32
    };
    for &n in &[16usize, 64] {
        let a: Vec<u32> = (0..n * n).map(|_| next()).collect();
        let b: Vec<u32> = (0..n * n).map(|_| next()).collect();
        let mut c1 = vec![0u32; n * n];
        let mut c2 = vec![0u32; n * n];
        naive_n(n, &a, &b, &mut c1);
        fast_n(n, 4, &a, &b, &mut c2);
        assert_eq!(c1, c2, "recursive mismatch at n={n}");
    }
    println!("field-verified: recursive rank-48 == naive at n=16, 64 over BabyBear");

    let sizes: &[usize] = if std::env::var("BENCH_BIG").is_ok() {
        &[4096]
    } else {
        &[16, 64, 256, 1024]
    };
    for &n in sizes {
        let a: Vec<u32> = (0..n * n).map(|_| next()).collect();
        let b: Vec<u32> = (0..n * n).map(|_| next()).collect();
        let mut c = vec![0u32; n * n];
        let reps = (200_000_000usize / (n * n * n)).max(1);
        let t0 = std::time::Instant::now();
        for _ in 0..reps {
            naive_n(n, &a, &b, &mut c);
        }
        let tn = t0.elapsed().as_secs_f64() / reps as f64;
        let tb0 = std::time::Instant::now();
        for _ in 0..reps {
            naive_blocked(n, &a, &b, &mut c);
        }
        let tnb = (tb0.elapsed().as_secs_f64() / reps as f64).min(tn);
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
            "n={n:5}  naive {:>9.3} ms  blocked {:>9.3} ms  rank48 {:>9.3} ms (cut {})  ratio-vs-blocked {:.2}",
            tn * 1e3,
            tnb * 1e3,
            best.0 * 1e3,
            best.1,
            best.0 / tnb
        );
    }
}
