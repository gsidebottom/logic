//! benchdr — calibrate the delayed-reduction cost model on real
//! silicon. Measures, over Goldilocks on this machine:
//!   scalar mul (mul+umulh+reduce128)      -> C_MUL
//!   deferred mul (mul+umulh, no reduce)   -> D_MUL
//!   (lo,hi) accumulate of a product       -> D_ACC
//!   final combine + reduce                -> D_COMB
//!   halving fdiv2                         -> C_HALF
//!   modular add                           -> C_ADD
//! plus an end-to-end 16-term dot product both ways (the honest
//! composite). Correctness gate: delayed dot == scalar dot on 100k
//! random cases before any timing.
const P: u64 = 0xFFFF_FFFF_0000_0001;

#[inline(always)]
fn reduce128(x: u128) -> u64 {
    let lo = x as u64;
    let hi = (x >> 64) as u64;
    let hi_hi = hi >> 32;
    let hi_lo = hi & 0xFFFF_FFFF;
    let t1 = hi_lo * 0xFFFF_FFFF;
    let mut s = lo as u128 + t1 as u128 + (P as u128 - hi_hi as u128);
    while s >= P as u128 {
        s -= P as u128;
    }
    s as u64
}
#[inline(always)]
fn fmul(a: u64, b: u64) -> u64 {
    reduce128(a as u128 * b as u128)
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
fn fdiv2(x: u64) -> u64 {
    (x >> 1) + (x & 1) * ((P + 1) >> 1)
}

/// deferred: sum products as (sum_lo, sum_hi) u128 accumulators;
/// combine = sum_lo + 2^64*sum_hi via two reductions folded into one
#[inline(always)]
fn dr_dot(a: &[u64], b: &[u64]) -> u64 {
    let mut slo: u128 = 0;
    let mut shi: u128 = 0;
    for (&x, &y) in a.iter().zip(b) {
        let p = x as u128 * y as u128;
        slo += p as u64 as u128;
        shi += (p >> 64) as u128;
    }
    // total = slo + 2^64 * shi  (mod p);  2^64 ≡ 2^32 − 1 (mod p)
    let r_lo = reduce128(slo);
    let r_hi = reduce128(shi);
    fadd(r_lo, fmul(r_hi, TWO64_MOD_P))
}
const TWO64_MOD_P: u64 = 0xFFFF_FFFF; // 2^64 ≡ 2^32 − 1 (mod p)

fn scalar_dot(a: &[u64], b: &[u64]) -> u64 {
    let mut s = 0u64;
    for (&x, &y) in a.iter().zip(b) {
        s = fadd(s, fmul(x, y));
    }
    s
}

fn bench<F: FnMut() -> u64>(name: &str, per_iter_ops: f64, mut f: F) -> f64 {
    let mut sink = 0u64;
    let reps = 2_000_000u64;
    // warmup
    for _ in 0..10_000 {
        sink ^= f();
    }
    let t0 = std::time::Instant::now();
    for _ in 0..reps {
        sink ^= f();
    }
    let ns = t0.elapsed().as_nanos() as f64 / reps as f64 / per_iter_ops;
    println!("{name:<34} {ns:6.3} ns/op   (sink {})", sink & 1);
    ns
}

fn main() {
    // gate: dr_dot == scalar_dot, 100k randoms, lengths 1..48
    let mut rng = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng % P
    };
    assert_eq!(fmul(TWO64_MOD_P, 1), (((1u128 << 64) % P as u128) as u64));
    for trial in 0..100_000 {
        let n = 1 + (trial % 48);
        let a: Vec<u64> = (0..n).map(|_| next()).collect();
        let b: Vec<u64> = (0..n).map(|_| next()).collect();
        assert_eq!(dr_dot(&a, &b), scalar_dot(&a, &b), "trial {trial}");
    }
    println!("gate: delayed dot == scalar dot on 100k random cases (len 1..48)");

    let xs: Vec<u64> = (0..64).map(|_| next()).collect();
    let ys: Vec<u64> = (0..64).map(|_| next()).collect();

    // per-op microbenches (16 dependent ops per closure call to
    // defeat OoO overlap illusions; per_iter_ops = 16)
    let mut x = xs[0];
    let y = ys[1] | 1;
    bench("scalar mul (C_MUL)", 16.0, || {
        for _ in 0..16 {
            x = fmul(x, y);
        }
        x
    });
    let mut acc_lo: u128 = 0;
    let mut acc_hi: u128 = 0;
    let mut xv = xs[2];
    bench("deferred mul+accum (D_MUL+D_ACC)", 16.0, || {
        for _ in 0..16 {
            let p = xv as u128 * y as u128;
            acc_lo += p as u64 as u128;
            acc_hi += (p >> 64) as u128;
            xv ^= acc_lo as u64;
        }
        xv
    });
    let mut c = xs[3];
    bench("combine+reduce (D_COMB)", 16.0, || {
        for _ in 0..16 {
            c = fadd(reduce128(c as u128 + acc_lo), fmul(reduce128(acc_hi), TWO64_MOD_P));
            acc_lo ^= c as u128;
        }
        c
    });
    let mut h = xs[4];
    bench("halving fdiv2 (C_HALF)", 16.0, || {
        for _ in 0..16 {
            h = fdiv2(h ^ 1);
        }
        h
    });
    let mut s = xs[5];
    bench("modular add (C_ADD)", 16.0, || {
        for _ in 0..16 {
            s = fadd(s, y);
        }
        s
    });

    // end-to-end 16-term dots (throughput style, independent data)
    let a16: Vec<u64> = xs[..16].to_vec();
    let b16: Vec<u64> = ys[..16].to_vec();
    let mut i = 0usize;
    bench("dot16 scalar (per term)", 16.0, || {
        i = (i + 1) & 31;
        scalar_dot(&a16, &b16)
    });
    bench("dot16 delayed (per term)", 16.0, || {
        i = (i + 1) & 31;
        dr_dot(&a16, &b16)
    });
    println!("\nmodel says: C_MUL 6.5 / D_MUL+D_ACC 4.0 / D_COMB 7.0 / C_HALF 2.0 / C_ADD 1.5 (in ~0.3ns cycles)");
    println!("if measured deferred-vs-scalar dot ratio << model ratio, delayed reduction is cheaper than modeled");
}
