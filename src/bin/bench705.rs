//! bench705 — model vs silicon for the machine-cost record flip.
//! Four single-tile 4x4 Goldilocks multipliers, all field-gated
//! against schoolbook naive on 20k random inputs before timing:
//!   naive4          64 mul + 48 add
//!   fast4_284       accurate triple, scalar (op-count record, 284)
//!   fast4_705s      ours triple, scalar (357 ops)
//!   fast4_705d      ours triple, DELAYED REDUCTION: 48 products
//!                   stay unreduced (lo,hi); P accumulates u128 limb
//!                   pairs with bound-tracked negation; one combine
//!                   per output.
//! machinecost predicts 284-scalar 753 vs ours-delayed 705 (0.94).
const P: u64 = 0xFFFF_FFFF_0000_0001;
const TWO64_MOD_P: u64 = 0xFFFF_FFFF; // 2^64 ≡ 2^32 − 1 (mod p)

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
fn fsub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a.wrapping_sub(b).wrapping_add(P) }
}
#[inline(always)]
fn fneg(a: u64) -> u64 {
    if a == 0 { 0 } else { P - a }
}
const INV2POW: [u64; 5] = [
    1,
    0x7FFF_FFFF_8000_0001,
    0xBFFF_FFFF_4000_0001,
    0xDFFF_FFFF_2000_0001,
    0xEFFF_FFFF_1000_0001,
];

mod m284 {
    use super::*;
    include!("../slp284.rs");
}
mod m705 {
    use super::*;
    include!("../slp705.rs");
}

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

fn fast4_284(a: &[u64; 16], b: &[u64; 16], c: &mut [u64; 16]) {
    let (mut la, mut rb, mut pr) = ([0u64; 48], [0u64; 48], [0u64; 48]);
    m284::slp_l(a, &mut la);
    m284::slp_r(b, &mut rb);
    for t in 0..48 {
        pr[t] = fmul(la[t], rb[t]);
    }
    m284::slp_p(&pr, c);
}

fn fast4_705s(a: &[u64; 16], b: &[u64; 16], c: &mut [u64; 16]) {
    let (mut la, mut rb, mut pr) = ([0u64; 48], [0u64; 48], [0u64; 48]);
    m705::slp_l(a, &mut la);
    m705::slp_r(b, &mut rb);
    for t in 0..48 {
        pr[t] = fmul(la[t], rb[t]);
    }
    m705::slp_p(&pr, c);
}

fn fast4_705d(a: &[u64; 16], b: &[u64; 16], c: &mut [u64; 16]) {
    let (mut la, mut rb) = ([0u64; 48], [0u64; 48]);
    m705::slp_l(a, &mut la);
    m705::slp_r(b, &mut rb);
    let (mut plo, mut phi) = ([0u64; 48], [0u64; 48]);
    for t in 0..48 {
        let p = la[t] as u128 * rb[t] as u128; // NO reduction
        plo[t] = p as u64;
        phi[t] = (p >> 64) as u64;
    }
    m705::dslp_p(&plo, &phi, c);
}

fn main() {
    let mut rng = 0x243f_6a88_85a3_08d3u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng % P
    };
    // field gates: 20k random tiles, all four agree with naive
    for trial in 0..20_000 {
        let mut a = [0u64; 16];
        let mut b = [0u64; 16];
        for i in 0..16 {
            a[i] = next();
            b[i] = next();
        }
        let (mut c0, mut c1, mut c2, mut c3) =
            ([0u64; 16], [0u64; 16], [0u64; 16], [0u64; 16]);
        naive4(&a, &b, &mut c0);
        fast4_284(&a, &b, &mut c1);
        fast4_705s(&a, &b, &mut c2);
        fast4_705d(&a, &b, &mut c3);
        assert_eq!(c0, c1, "284 mismatch at {trial}");
        assert_eq!(c0, c2, "705s mismatch at {trial}");
        assert_eq!(c0, c3, "705d (delayed) mismatch at {trial}");
    }
    println!("field-gated: 284-scalar, ours-scalar, ours-DELAYED all == naive on 20k random tiles");

    let reps = 2_000_000u64;
    let mut run = |name: &str, f: &dyn Fn(&[u64; 16], &[u64; 16], &mut [u64; 16])| -> f64 {
        let mut a = [0u64; 16];
        let mut b = [0u64; 16];
        for i in 0..16 {
            a[i] = next();
            b[i] = next();
        }
        let mut c = [0u64; 16];
        let mut sink = 0u64;
        for _ in 0..20_000 {
            f(&a, &b, &mut c);
            sink ^= c[0];
            a[0] = fadd(a[0], 1);
        }
        let t0 = std::time::Instant::now();
        for _ in 0..reps {
            f(&a, &b, &mut c);
            sink ^= c[0];
            a[0] = fadd(a[0], 1);
        }
        let ns = t0.elapsed().as_nanos() as f64 / reps as f64;
        println!("{name:<22} {ns:8.1} ns/tile   (sink {})", sink & 1);
        ns
    };
    let tn = run("naive4", &naive4);
    let t284 = run("284 scalar", &fast4_284);
    let t705s = run("ours scalar (357 op)", &fast4_705s);
    let t705d = run("ours DELAYED", &fast4_705d);
    println!();
    println!(
        "measured ratios vs 284-scalar: ours-scalar {:.3}  ours-DELAYED {:.3}",
        t705s / t284,
        t705d / t284
    );
    println!(
        "model predicted: ours-scalar {:.3}  ours-DELAYED {:.3}   (naive/284 measured {:.3})",
        1107.9 / 999.6,
        705.2 / 752.8,
        tn / t284
    );
}
