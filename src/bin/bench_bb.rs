//! bench_bb — BabyBear witness-generation arm: 4x32-bit lane batching
//! ACROSS tiles (the throughput-shaped SIMD the Goldilocks refutation
//! left standing). Montgomery arithmetic (R = 2^32); the 284-op
//! rank-48 networks come from the El-generic codegen (slp284g.rs), so
//! the same gated SLP runs on scalars Bb and 4-lane batches Bb4.
//! Gates before timing:
//!   1. Montgomery mul vs (a*b) % p on 1M randoms
//!   2. scalar fast4-284 == scalar naive4 on 10k tiles
//!   3. batched (Bb4) naive4/fast4 == 4x scalar on 10k tile-quads
//! Then ns/tile for {naive4, 284} x {scalar, 4-lane}.
#![allow(non_camel_case_types)]

const P: u32 = 0x7800_0001; // BabyBear 2^31 - 2^27 + 1
const P64: u64 = P as u64;

#[inline(always)]
fn mont_mul(a: u32, b: u32, np: u32) -> u32 {
    let t = a as u64 * b as u64;
    let m = (t as u32).wrapping_mul(np);
    let t2 = ((t + m as u64 * P64) >> 32) as u32;
    if t2 >= P { t2 - P } else { t2 }
}
#[inline(always)]
fn badd(a: u32, b: u32) -> u32 {
    let s = a + b; // a,b < p < 2^31: no u32 overflow
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

fn pow_mod(mut b: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    b %= P64;
    while e > 0 {
        if e & 1 == 1 {
            r = r * b % P64;
        }
        b = b * b % P64;
        e >>= 1;
    }
    r
}

struct Ctx {
    np: u32,
    r2: u32,          // R^2 mod p (to_mont multiplier)
    inv2m: [u32; 5],  // Montgomery-form (1/2)^k
}

fn ctx() -> Ctx {
    // p' = -p^{-1} mod 2^32 by Newton iteration
    let mut inv: u32 = 1;
    for _ in 0..5 {
        inv = inv.wrapping_mul(2u32.wrapping_sub(P.wrapping_mul(inv)));
    }
    let np = inv.wrapping_neg();
    assert_eq!(P.wrapping_mul(np), u32::MAX - 0, "np check"); // p*np ≡ -1 mod 2^32
    let r2 = ((1u128 << 64) % P as u128) as u32;
    let inv2 = pow_mod(2, P64 - 2);
    let mut inv2m = [0u32; 5];
    for k in 0..5 {
        let v = pow_mod(inv2, k as u64) as u128;
        inv2m[k] = ((v << 32) % P as u128) as u32;
    }
    Ctx { np, r2, inv2m }
}

// ---- element types for the generic SLP ----
pub trait El: Clone {
    fn add(&self, o: &Self) -> Self;
    fn sub(&self, o: &Self) -> Self;
    fn neg(&self) -> Self;
    fn scale2(&self, k: i32) -> Self;
}

static NP_G: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
static INV2M_G: std::sync::OnceLock<[u32; 5]> = std::sync::OnceLock::new();

#[derive(Clone, Copy, PartialEq, Debug)]
struct Bb(u32);
impl El for Bb {
    fn add(&self, o: &Self) -> Self {
        Bb(badd(self.0, o.0))
    }
    fn sub(&self, o: &Self) -> Self {
        Bb(bsub(self.0, o.0))
    }
    fn neg(&self) -> Self {
        Bb(bneg(self.0))
    }
    fn scale2(&self, k: i32) -> Self {
        if k >= 0 {
            let mut v = self.0;
            for _ in 0..k {
                v = badd(v, v);
            }
            Bb(v)
        } else {
            let np = *NP_G.get().unwrap();
            let c = INV2M_G.get().unwrap()[(-k) as usize];
            Bb(mont_mul(self.0, c, np))
        }
    }
}

#[derive(Clone, Copy, PartialEq, Debug)]
struct Bb4([u32; 4]);
impl El for Bb4 {
    #[inline(always)]
    fn add(&self, o: &Self) -> Self {
        let mut r = [0u32; 4];
        for i in 0..4 {
            r[i] = badd(self.0[i], o.0[i]);
        }
        Bb4(r)
    }
    #[inline(always)]
    fn sub(&self, o: &Self) -> Self {
        let mut r = [0u32; 4];
        for i in 0..4 {
            r[i] = bsub(self.0[i], o.0[i]);
        }
        Bb4(r)
    }
    #[inline(always)]
    fn neg(&self) -> Self {
        let mut r = [0u32; 4];
        for i in 0..4 {
            r[i] = bneg(self.0[i]);
        }
        Bb4(r)
    }
    #[inline(always)]
    fn scale2(&self, k: i32) -> Self {
        if k >= 0 {
            let mut v = *self;
            for _ in 0..k {
                v = v.add(&v);
            }
            v
        } else {
            let np = *NP_G.get().unwrap();
            let c = INV2M_G.get().unwrap()[(-k) as usize];
            let mut r = [0u32; 4];
            for i in 0..4 {
                r[i] = mont_mul(self.0[i], c, np);
            }
            Bb4(r)
        }
    }
}

#[inline(always)]
fn mul4_scalar(a: &Bb4, b: &Bb4, np: u32) -> Bb4 {
    let mut r = [0u32; 4];
    for i in 0..4 {
        r[i] = mont_mul(a.0[i], b.0[i], np);
    }
    Bb4(r)
}

/// 4-lane Montgomery multiply via NEON widening mults. Overflow-safe:
/// t < 2^62, m*p < 2^63, sum < 2^64; result < 2p < 2^32 after >>32.
#[cfg(target_arch = "aarch64")]
#[inline(always)]
fn mul4(a: &Bb4, b: &Bb4, np: u32) -> Bb4 {
    use std::arch::aarch64::*;
    unsafe {
        let av = vld1q_u32(a.0.as_ptr());
        let bv = vld1q_u32(b.0.as_ptr());
        let npd = vdup_n_u32(np);
        let pd = vdup_n_u32(P);
        let t01 = vmull_u32(vget_low_u32(av), vget_low_u32(bv));
        let t23 = vmull_u32(vget_high_u32(av), vget_high_u32(bv));
        let m01 = vmul_u32(vmovn_u64(t01), npd);
        let m23 = vmul_u32(vmovn_u64(t23), npd);
        let s01 = vaddq_u64(t01, vmull_u32(m01, pd));
        let s23 = vaddq_u64(t23, vmull_u32(m23, pd));
        let r01 = vshrn_n_u64(s01, 32);
        let r23 = vshrn_n_u64(s23, 32);
        let r = vcombine_u32(r01, r23);
        // conditional subtract p: min(r, r - p) in unsigned wrap
        let res = vminq_u32(r, vsubq_u32(r, vdupq_n_u32(P)));
        let mut out = [0u32; 4];
        vst1q_u32(out.as_mut_ptr(), res);
        Bb4(out)
    }
}
#[cfg(not(target_arch = "aarch64"))]
#[inline(always)]
fn mul4(a: &Bb4, b: &Bb4, np: u32) -> Bb4 {
    mul4_scalar(a, b, np)
}

mod g284 {
    use super::El;
    include!("../slp284g.rs");
}

fn naive4_g<T: El>(mul: &dyn Fn(&T, &T) -> T, a: &[T], b: &[T]) -> Vec<T> {
    let mut c = Vec::with_capacity(16);
    for i in 0..4 {
        for j in 0..4 {
            let mut s = mul(&a[4 * i], &b[j]);
            for k in 1..4 {
                s = s.add(&mul(&a[4 * i + k], &b[4 * k + j]));
            }
            c.push(s);
        }
    }
    c
}

fn fast4_g<T: El + Default + Copy>(mul: &dyn Fn(&T, &T) -> T, a: &[T], b: &[T]) -> Vec<T> {
    let mut la = vec![T::default(); 48];
    let mut rb = vec![T::default(); 48];
    g284::gslp_l(a, &mut la);
    g284::gslp_r(b, &mut rb);
    let pr: Vec<T> = (0..48).map(|t| mul(&la[t], &rb[t])).collect();
    let mut c = vec![T::default(); 16];
    g284::gslp_p(&pr, &mut c);
    c
}

impl Default for Bb {
    fn default() -> Self {
        Bb(0)
    }
}
impl Default for Bb4 {
    fn default() -> Self {
        Bb4([0; 4])
    }
}

fn main() {
    let cx = ctx();
    NP_G.set(cx.np).unwrap();
    INV2M_G.set(cx.inv2m).unwrap();
    let np = cx.np;
    let to_m = |x: u32| mont_mul(x, cx.r2, np);
    let from_m = |x: u32| mont_mul(x, 1, np);

    let mut rng = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        (rng % P64) as u32
    };

    // gate 1: mont mul vs reference
    for _ in 0..1_000_000 {
        let a = next();
        let b = next();
        let got = from_m(mont_mul(to_m(a), to_m(b), np));
        assert_eq!(got as u64, a as u64 * b as u64 % P64);
    }
    println!("gate 1: Montgomery mul == (a*b) % p on 1M randoms");

    // gate 2: scalar 284 == scalar naive on 10k tiles
    let smul = |a: &Bb, b: &Bb| Bb(mont_mul(a.0, b.0, np));
    for _ in 0..10_000 {
        let a: Vec<Bb> = (0..16).map(|_| Bb(to_m(next()))).collect();
        let b: Vec<Bb> = (0..16).map(|_| Bb(to_m(next()))).collect();
        assert_eq!(naive4_g(&smul, &a, &b), fast4_g(&smul, &a, &b));
    }
    println!("gate 2: BabyBear scalar 284-SLP == naive on 10k tiles");

    // gate 3a: NEON mont mul4 == scalar mont per lane, 1M random quads
    for _ in 0..1_000_000 {
        let x = Bb4([to_m(next()), to_m(next()), to_m(next()), to_m(next())]);
        let y = Bb4([to_m(next()), to_m(next()), to_m(next()), to_m(next())]);
        assert_eq!(mul4(&x, &y, np), mul4_scalar(&x, &y, np));
    }
    println!("gate 3a: NEON mul4 == scalar Montgomery per lane on 1M quads");

    // gate 3: batched == 4x scalar
    let vmul = |a: &Bb4, b: &Bb4| mul4(a, b, np);
    for _ in 0..10_000 {
        let a4: Vec<Bb4> = (0..16)
            .map(|_| Bb4([to_m(next()), to_m(next()), to_m(next()), to_m(next())]))
            .collect();
        let b4: Vec<Bb4> = (0..16)
            .map(|_| Bb4([to_m(next()), to_m(next()), to_m(next()), to_m(next())]))
            .collect();
        let c4 = fast4_g(&vmul, &a4, &b4);
        for lane in 0..4 {
            let a: Vec<Bb> = a4.iter().map(|x| Bb(x.0[lane])).collect();
            let b: Vec<Bb> = b4.iter().map(|x| Bb(x.0[lane])).collect();
            let c = fast4_g(&smul, &a, &b);
            for z in 0..16 {
                assert_eq!(c[z].0, c4[z].0[lane]);
            }
        }
    }
    println!("gate 3: 4-lane batched 284-SLP == per-lane scalar on 10k tile-quads");

    // ---- timing ----
    let reps = 1_000_000u64;
    let a: Vec<Bb> = (0..16).map(|_| Bb(to_m(next()))).collect();
    let b: Vec<Bb> = (0..16).map(|_| Bb(to_m(next()))).collect();
    let a4: Vec<Bb4> = (0..16)
        .map(|i| Bb4([a[i].0, to_m(next()), to_m(next()), to_m(next())]))
        .collect();
    let b4: Vec<Bb4> = (0..16)
        .map(|i| Bb4([b[i].0, to_m(next()), to_m(next()), to_m(next())]))
        .collect();

    let time = |name: &str, tiles_per_call: f64, f: &mut dyn FnMut() -> u32| {
        let mut sink = 0u32;
        for _ in 0..10_000 {
            sink ^= f();
        }
        let t0 = std::time::Instant::now();
        for _ in 0..reps {
            sink ^= f();
        }
        let ns = t0.elapsed().as_nanos() as f64 / reps as f64 / tiles_per_call;
        println!("{name:<28} {ns:8.1} ns/tile   (sink {})", sink & 1);
        ns
    };

    let mut aa = a.clone();
    let t_ns = time("BB naive4 scalar", 1.0, &mut || {
        aa[0] = aa[0].add(&Bb(1));
        naive4_g(&smul, &aa, &b)[0].0
    });
    let mut aa = a.clone();
    let t_fs = time("BB 284 scalar", 1.0, &mut || {
        aa[0] = aa[0].add(&Bb(1));
        fast4_g(&smul, &aa, &b)[0].0
    });
    let mut aa4 = a4.clone();
    let t_n4 = time("BB naive4 4-lane", 4.0, &mut || {
        aa4[0].0[0] = badd(aa4[0].0[0], 1);
        naive4_g(&vmul, &aa4, &b4)[0].0[0]
    });
    let mut aa4 = a4.clone();
    let t_f4 = time("BB 284 4-lane", 4.0, &mut || {
        aa4[0].0[0] = badd(aa4[0].0[0], 1);
        fast4_g(&vmul, &aa4, &b4)[0].0[0]
    });
    println!();
    println!(
        "lane speedup: naive {:.2}x  284 {:.2}x   (Goldilocks scalar refs: naive 197.8, 284 282.0 ns/tile)",
        t_ns / t_n4,
        t_fs / t_f4
    );
    println!(
        "cross-field per-tile: BB-4lane naive {:.1} vs G naive 197.8 -> {:.2}x ; BB-4lane 284 {:.1} vs G 284 282.0 -> {:.2}x",
        t_n4, 197.8 / t_n4, t_f4, 282.0 / t_f4
    );
}
