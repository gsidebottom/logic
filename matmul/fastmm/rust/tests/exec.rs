//! Every kind of plan against Accelerate's GEMM at small sizes: fused levels (square and
//! rectangular, the 3x3x6 family's three orientations), streams, pipelines, the classical
//! blocked leaf, leading dimensions larger than the matrices and padding, and the entry points.
//!
//!   cargo test --release

use fmm::exec;
use fmm::{Plan, Real, Shape};

fn inputs<T: Real>(na: usize, nb: usize, seed: u64) -> (Vec<T>, Vec<T>) {
    let mut s = seed;
    let mut rnd = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        T::from_f64((s >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0)
    };
    let a = (0..na).map(|_| rnd()).collect();
    let b = (0..nb).map(|_| rnd()).collect();
    (a, b)
}

/// C = A B on shape s by the plan at the padded shape sp (A m x k with leading dimension lda, B
/// k x n with ldb, C m x n with ldc), against Accelerate's product: the max-norm difference
/// relative to the product's largest entry
fn check<T: Real>(plan: &str, s: Shape, sp: Shape, lda: usize, ldb: usize, ldc: usize) -> f64 {
    let p = Plan::parse(plan).unwrap();
    assert!(p.divides(sp), "{plan} does not divide {sp}");
    let (a, b) = inputs::<T>(s.m * lda, s.k * ldb, 0x9e3779b97f4a7c15 ^ (s.m * 31 + s.k * 7 + s.n) as u64);
    let mut c = vec![T::default(); s.m * ldc];
    let mut r = vec![T::default(); s.m * ldc];
    let mut work = vec![T::default(); exec::padded_work(&p, s, sp)];
    fmm::in_pool(|| exec::exec_padded(&p.0, s, sp, &a, lda, &b, ldb, &mut c, ldc, &mut work));
    T::gemm(s, &a, lda, &b, ldb, 0.0, &mut r, ldc);
    let (mut err, mut mx) = (0.0f64, 0.0f64);
    for i in 0..s.m {
        for j in 0..s.n {
            err = err.max((c[i * ldc + j].to_f64() - r[i * ldc + j].to_f64()).abs());
            mx = mx.max(r[i * ldc + j].to_f64().abs());
        }
    }
    err / mx
}

fn sq<T: Real>(plan: &str, n: usize) -> f64 {
    check::<T>(plan, Shape::sq(n), Shape::sq(n), n, n, n)
}

/// square problems: 1024 and 2048 for the 2x2 and 4x4 levels, 1080 = 54 * 20 and 1296 = 54 * 24
/// for the 3x3x6 family (its cycle divides by 54), 1152 = 4 * 288 for mixed plans
const PLANS: [(&str, usize); 21] = [
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
    ("R336/G", 1080),
    ("R363/G6", 1080),
    ("R633/G3", 1080),
    ("R336/R363/R633/G", 1296),
    ("R363+3/R633/G6", 1296),
    ("SW/R363/G", 1296),
    ("SW+3/R363/G6", 1296),
    ("D48/R336/G", 1152),
    ("R336+2/D48/G3", 1152),
];

/// rectangular problems (m, k, n)
const RECT: [(&str, (usize, usize, usize)); 7] = [
    ("G", (300, 500, 200)),
    ("D48/G6", (512, 1024, 256)),
    ("SW+2/D48/G3", (1024, 2048, 512)),
    ("R336/G", (900, 300, 1200)),
    ("R363/D48/G6", (768, 1536, 384)),
    ("R633+2/SW/G4", (1152, 576, 288)),
    ("D48+3/R363/G6", (1152, 2304, 576)),
];

#[test]
fn plans_f64() {
    for (plan, n) in PLANS {
        let e = sq::<f64>(plan, n);
        assert!(e < 1e-12, "{plan} at {n}: {e:e}");
    }
    for (plan, (m, k, n)) in RECT {
        let s = Shape::new(m, k, n);
        let e = check::<f64>(plan, s, s, k, n, n);
        assert!(e < 1e-12, "{plan} at {s}: {e:e}");
    }
}

#[test]
fn plans_f32() {
    for (plan, n) in PLANS {
        let e = sq::<f32>(plan, n);
        assert!(e < 1e-4, "{plan} at {n}: {e:e}");
    }
    for (plan, (m, k, n)) in RECT {
        let s = Shape::new(m, k, n);
        let e = check::<f32>(plan, s, s, k, n, n);
        assert!(e < 1e-4, "{plan} at {s}: {e:e}");
    }
}

#[test]
fn leading_dimensions_and_padding() {
    assert!(check::<f64>("D48/G6", Shape::sq(1024), Shape::sq(1024), 1064, 1064, 1064) < 1e-12);
    assert!(check::<f64>("SW+3/D48/G6", Shape::sq(2048), Shape::sq(2048), 2056, 2056, 2056) < 1e-12);
    assert!(check::<f64>("D48/G6", Shape::sq(1000), Shape::sq(1024), 1000, 1000, 1000) < 1e-12);
    assert!(check::<f32>("SW/G3", Shape::sq(1001), Shape::sq(1024), 1003, 1003, 1003) < 1e-4);
    // rectangular: each leading dimension its own, padded to a shape the plan divides
    assert!(check::<f32>("R336/G", Shape::new(900, 300, 1200), Shape::new(900, 300, 1200), 310, 1210, 1205) < 1e-4);
    assert!(check::<f64>("D48/G6", Shape::new(1000, 3000, 2000), Shape::new(1024, 3072, 2048), 3000, 2000, 2000) < 1e-12);
    assert!(check::<f64>("R363/R633/G", Shape::new(1000, 2000, 500), Shape::new(1026, 2016, 504), 2000, 500, 500) < 1e-12);
}

#[test]
fn entry_points() {
    // n = 300 is below every fused level (blocks of at least 256), so whatever the calibration
    // cache holds the call is correct; shapes are checked
    let n = 300;
    let (a, b) = inputs::<f64>(n * n, n * n, 7);
    let mut c = vec![0.0; n * n];
    fmm::dgemm(n, &a, n, &b, n, &mut c, n, 0.0).unwrap();
    let mut r = vec![0.0; n * n];
    f64::gemm(Shape::sq(n), &a, n, &b, n, 0.0, &mut r, n);
    let err = c.iter().zip(&r).fold(0.0f64, |m, (x, y)| m.max((x - y).abs()));
    assert!(err < 1e-12 * n as f64, "{err:e}");
    assert_eq!(fmm::dgemm(n, &a, n - 1, &b, n, &mut c, n, 0.0),
               Err(fmm::Error::Shape("a leading dimension is below its matrix's columns")));
    assert_eq!(fmm::dgemm(n, &a[1..], n, &b, n, &mut c, n, 0.0), Err(fmm::Error::Shape("a slice is too short for its matrix")));
    assert_eq!(fmm::sgemm(0, &[], 0, &[], 0, &mut [], 0, 0.0), Ok(()));
    // a rectangular problem through the m, k, n entry point, with its own leading dimensions
    let (m, k, n) = (200, 300, 100);
    let (lda, ldb, ldc) = (k + 3, n + 5, n + 1);
    let (a, b) = inputs::<f32>(m * lda, k * ldb, 11);
    let mut c = vec![0.0f32; m * ldc];
    fmm::sgemm_mkn(m, k, n, &a, lda, &b, ldb, &mut c, ldc, 0.0).unwrap();
    let mut r = vec![0.0f32; m * ldc];
    f32::gemm(Shape::new(m, k, n), &a, lda, &b, ldb, 0.0, &mut r, ldc);
    let err = (0..m).flat_map(|i| (0..n).map(move |j| i * ldc + j)).fold(0.0f32, |e, x| e.max((c[x] - r[x]).abs()));
    assert!(err < 1e-4 * k as f32, "{err:e}");
    assert_eq!(fmm::sgemm_mkn(m, k, n, &a[..m * k - 1], k, &b, ldb, &mut c, ldc, 0.0),
               Err(fmm::Error::Shape("a slice is too short for its matrix")));
    assert_eq!(fmm::sgemm_mkn(m, k, n, &a, lda, &b, n - 1, &mut c, ldc, 0.0),
               Err(fmm::Error::Shape("a leading dimension is below its matrix's columns")));
    // empty dimensions: m or n = 0 does nothing, k = 0 zeroes C
    assert_eq!(fmm::dgemm_mkn(0, 5, 7, &[], 5, &[], 7, &mut [], 7, 0.0), Ok(()));
    let mut c = vec![1.0f64; 2 * 3];
    assert_eq!(fmm::dgemm_mkn(2, 0, 3, &[], 0, &[], 3, &mut c, 3, 0.0), Ok(()));
    assert!(c.iter().all(|&x| x == 0.0));
    let info = fmm::plan_mkn(300, 300, 300, true, 0.0);
    assert_eq!(info.spad, Shape::sq(300));
    assert_eq!(fmm::plan(300, true, 0.0).plan, info.plan);
}
