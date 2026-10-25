//! Every kind of plan against Accelerate's GEMM at small sizes: fused levels, streams,
//! pipelines, the classical blocked leaf, leading dimensions larger than n and padding.
//!
//!   cargo test --release

use fmm::exec;
use fmm::{Plan, Real};

fn inputs<T: Real>(n: usize, ld: usize, seed: u64) -> (Vec<T>, Vec<T>) {
    let mut s = seed;
    let mut rnd = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        T::from_f64((s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0)
    };
    let a = (0..n * ld).map(|_| rnd()).collect();
    let b = (0..n * ld).map(|_| rnd()).collect();
    (a, b)
}

/// the max-norm difference from Accelerate's product, relative to the product's largest entry
fn check<T: Real>(plan: &str, n: usize, npad: usize, ld: usize) -> f64 {
    let p = Plan::parse(plan).unwrap();
    let (a, b) = inputs::<T>(n, ld, 0x9e3779b97f4a7c15 ^ n as u64);
    let mut c = vec![T::default(); n * ld];
    let mut r = vec![T::default(); n * ld];
    let mut work = vec![T::default(); exec::padded_work(&p, n, npad)];
    fmm::in_pool(|| exec::exec_padded(&p.0, n, npad, &a, ld, &b, ld, &mut c, ld, &mut work));
    T::gemm(n, &a, ld, &b, ld, 0.0, &mut r, ld);
    let (mut err, mut mx) = (0.0f64, 0.0f64);
    for i in 0..n {
        for j in 0..n {
            err = err.max((c[i * ld + j].to_f64() - r[i * ld + j].to_f64()).abs());
            mx = mx.max(r[i * ld + j].to_f64().abs());
        }
    }
    err / mx
}

const PLANS: [(&str, usize); 12] = [
    ("G", 1024),
    ("B2", 1024),
    ("SW/G", 1024),
    ("D48/G", 1024),
    ("SW/G3", 1024),
    ("D48/G6", 1024),
    ("SW/SW/G4", 2048),
    ("SW+3/D48/G6", 2048),
    ("D48+2/SW/G3", 2048),
    ("D48+4/SW/G6", 2048),
    ("SW+/SW/G4", 2048),
    ("D48/SW/B2", 2048),
];

#[test]
fn plans_f64() {
    for (plan, n) in PLANS {
        let e = check::<f64>(plan, n, n, n);
        assert!(e < 1e-12, "{plan} at {n}: {e:e}");
    }
}

#[test]
fn plans_f32() {
    for (plan, n) in PLANS {
        let e = check::<f32>(plan, n, n, n);
        assert!(e < 1e-4, "{plan} at {n}: {e:e}");
    }
}

#[test]
fn leading_dimensions_and_padding() {
    assert!(check::<f64>("D48/G6", 1024, 1024, 1024 + 40) < 1e-12);
    assert!(check::<f64>("SW+3/D48/G6", 2048, 2048, 2048 + 8) < 1e-12);
    assert!(check::<f64>("D48/G6", 1000, 1024, 1000) < 1e-12);
    assert!(check::<f32>("SW/G3", 1001, 1024, 1003) < 1e-4);
}

#[test]
fn entry_points() {
    // n = 300 is below every fused level (blocks of at least 256), so whatever the calibration
    // cache holds the call is correct; shapes are checked
    let n = 300;
    let (a, b) = inputs::<f64>(n, n, 7);
    let mut c = vec![0.0; n * n];
    fmm::dgemm(n, &a, n, &b, n, &mut c, n, 0.0).unwrap();
    let mut r = vec![0.0; n * n];
    f64::gemm(n, &a, n, &b, n, 0.0, &mut r, n);
    let err = c.iter().zip(&r).fold(0.0f64, |m, (x, y)| m.max((x - y).abs()));
    assert!(err < 1e-12 * n as f64, "{err:e}");
    assert_eq!(fmm::dgemm(n, &a, n - 1, &b, n, &mut c, n, 0.0), Err(fmm::Error::Shape("a leading dimension is below n")));
    assert_eq!(fmm::dgemm(n, &a[1..], n, &b, n, &mut c, n, 0.0), Err(fmm::Error::Shape("a slice is too short for its matrix")));
    assert_eq!(fmm::sgemm(0, &[], 0, &[], 0, &mut [], 0, 0.0), Ok(()));
}
