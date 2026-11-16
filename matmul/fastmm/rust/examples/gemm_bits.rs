//! Does Accelerate's GEMM give the same bits for a shape from different threads and threading
//! settings?  dgemm/sgemm of (m x k)(k x n): on the main thread, on the library's pool, and
//! single-threaded; counts the entries that differ from the main thread's.
//!   cargo run --release --example gemm_bits [m k n]
use fmm::{Real, Shape};
fn run<T: Real>(s: Shape) {
    let mut x = 0x2545f4914f6cdd1du64;
    let mut u = || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; T::from_f64((x >> 11) as f64 / 9007199254740992.0 * 2.0 - 1.0) };
    let a: Vec<T> = (0..s.m * s.k).map(|_| u()).collect();
    let b: Vec<T> = (0..s.k * s.n).map(|_| u()).collect();
    let g = |single: bool| { let mut c = vec![T::default(); s.m * s.n]; fmm::sys::set_single_threaded(single); T::gemm(s, &a, s.k, &b, s.n, 0.0, &mut c, s.n); fmm::sys::set_single_threaded(false); c };
    let main = g(false);
    let single = g(true);
    let pooled = fmm::in_pool(|| g(false));
    let pooled1 = fmm::in_pool(|| g(true));
    let d = |c: &[T]| c.iter().zip(&main).filter(|(p, q)| p != q).count();
    println!("{} {s}: main-thread threaded vs single-threaded {}  vs pool threaded {}  vs pool single {}", if T::F64 { "f64" } else { "f32" },
             d(&single), d(&pooled), d(&pooled1));
}
fn main() {
    let v: Vec<usize> = std::env::args().skip(1).filter_map(|s| s.parse().ok()).collect();
    let shapes = if v.len() == 3 { vec![Shape::new(v[0], v[1], v[2])] } else {
        vec![Shape::new(2304, 2304, 1152), Shape::new(2304, 1152, 2304), Shape::new(1152, 2304, 2304), Shape::sq(1728), Shape::new(4608, 4608, 2304)]
    };
    for s in shapes { run::<f64>(s); run::<f32>(s); }
}
