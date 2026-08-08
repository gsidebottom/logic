//! bench315 — Goldilocks witness-generation microbenchmark for the
//! rank-48 networks (PLinOpt 315-op SLPs, codegen'd in slp315.rs)
//! against the naive 4x4 block multiply. Correctness gate first:
//! fast4 == naive4 on random field inputs (an independent field
//! verification of the distributed artifact); then timing.
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
#[allow(dead_code)]
fn fneg(a: u64) -> u64 {
    if a == 0 { 0 } else { P - a }
}

// INV2POW[k] = (1/2)^k mod P
const INV2POW: [u64; 4] = [
    1,
    0x7FFF_FFFF_8000_0001, // 1/2
    0xBFFF_FFFF_4000_0001, // 1/4  (computed below in main check)
    0xDFFF_FFFF_2000_0001, // 1/8
];

include!("../slp315.rs");

fn naive4(a: &[u64; 16], b: &[u64; 16], c: &mut [u64; 16]) {
    for i in 0..4 {
        for j in 0..4 {
            let mut s = 0u64;
            for k in 0..4 {
                s = fadd(s, fmul(a[4 * i + k], b[4 * k + j]));
            }
            c[4 * i + j] = s;
        }
    }
}

fn fast4(a: &[u64; 16], b: &[u64; 16], c: &mut [u64; 16]) {
    let mut la = [0u64; 48];
    let mut rb = [0u64; 48];
    slp_l(a, &mut la);
    slp_r(b, &mut rb);
    let mut pr = [0u64; 48];
    for t in 0..48 {
        pr[t] = fmul(la[t], rb[t]);
    }
    slp_p(&pr, c);
}

fn main() {
    // verify INV2POW
    let inv2 = {
        // 1/2 = (P+1)/2
        (P + 1) / 2
    };
    assert_eq!(INV2POW[1], inv2, "INV2POW[1]");
    assert_eq!(INV2POW[2], fmul(inv2, inv2), "INV2POW[2]");
    assert_eq!(INV2POW[3], fmul(fmul(inv2, inv2), inv2), "INV2POW[3]");

    let mut rng = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng % P
    };

    // correctness gate: 10_000 random pairs
    for trial in 0..10_000 {
        let mut a = [0u64; 16];
        let mut b = [0u64; 16];
        for i in 0..16 {
            a[i] = next();
            b[i] = next();
        }
        let mut c1 = [0u64; 16];
        let mut c2 = [0u64; 16];
        naive4(&a, &b, &mut c1);
        fast4(&a, &b, &mut c2);
        assert_eq!(c1, c2, "MISMATCH at trial {trial}");
    }
    println!("field-verified: fast4 == naive4 on 10,000 random Goldilocks inputs");

    // timing
    let n = 2_000_000u64;
    let mut a = [0u64; 16];
    let mut b = [0u64; 16];
    for i in 0..16 {
        a[i] = next();
        b[i] = next();
    }
    let mut sink = 0u64;
    let t0 = std::time::Instant::now();
    let mut c = [0u64; 16];
    for _ in 0..n {
        naive4(&a, &b, &mut c);
        sink ^= c[0];
        a[0] = fadd(a[0], 1);
    }
    let t_naive = t0.elapsed().as_nanos() as f64 / n as f64;
    let t1 = std::time::Instant::now();
    for _ in 0..n {
        fast4(&a, &b, &mut c);
        sink ^= c[0];
        a[0] = fadd(a[0], 1);
    }
    let t_fast = t1.elapsed().as_nanos() as f64 / n as f64;
    println!("single 4x4 tile over Goldilocks: naive {t_naive:.1} ns   315-SLP {t_fast:.1} ns   ratio {:.2}  (sink {sink})", t_fast / t_naive);
    println!("(naive: 64 mul + 48 add; fast: 48 mul + ~264 add + 27 cmul — single-tile naive SHOULD win;");
    println!(" the fast scheme pays off through recursion: mult count 48^d vs 64^d compounds at depth)");
}
