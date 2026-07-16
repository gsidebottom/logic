//! benchntt_bb — BabyBear radix-2 NTT curve (two-adicity 2^27),
//! completing the Appendix B field table next to benchntt_g
//! (Goldilocks) and benchzk's BN254-Fr curves. Montgomery
//! arithmetic; generator 31. Same gates as benchntt_g: root orders,
//! naive-DFT cross-check, round-trip identity, polynomial product
//! vs schoolbook. Usage: benchntt_bb [max_log2 (default 25)]
const P: u32 = 0x7800_0001; // 2^31 - 2^27 + 1
const P64: u64 = P as u64;

const fn np_const() -> u32 {
    // -p^{-1} mod 2^32 by Newton iteration
    let mut inv: u32 = 1;
    let mut i = 0;
    while i < 5 {
        inv = inv.wrapping_mul(2u32.wrapping_sub(P.wrapping_mul(inv)));
        i += 1;
    }
    inv.wrapping_neg()
}
const NP: u32 = np_const();
const R2: u32 = ((1u128 << 64) % P as u128) as u32; // R^2 mod p

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
fn to_m(x: u32) -> u32 {
    mmul(x, R2)
}
fn from_m(x: u32) -> u32 {
    mmul(x, 1)
}
fn mpow(mut b: u32, mut e: u64) -> u32 {
    // b in Montgomery form; result in Montgomery form
    let mut r = to_m(1);
    while e > 0 {
        if e & 1 == 1 {
            r = mmul(r, b);
        }
        b = mmul(b, b);
        e >>= 1;
    }
    r
}
fn minv(a: u32) -> u32 {
    mpow(a, P64 - 2)
}

/// in-place iterative Cooley–Tukey over Montgomery-form values
fn ntt(a: &mut [u32], root: u32) {
    let n = a.len();
    let lg = n.trailing_zeros();
    for i in 0..n {
        let j = (i as u32).reverse_bits() >> (32 - lg);
        if (j as usize) > i {
            a.swap(i, j as usize);
        }
    }
    let mut len = 2;
    while len <= n {
        let w_len = mpow(root, (n / len) as u64);
        for start in (0..n).step_by(len) {
            let mut w = to_m(1);
            for k in 0..len / 2 {
                let u = a[start + k];
                let v = mmul(a[start + k + len / 2], w);
                a[start + k] = badd(u, v);
                a[start + k + len / 2] = bsub(u, v);
                w = mmul(w, w_len);
            }
        }
        len <<= 1;
    }
}

fn intt(a: &mut [u32], root: u32) {
    let n = a.len() as u64;
    ntt(a, minv(root));
    let ninv = minv(to_m((n % P64) as u32));
    for x in a.iter_mut() {
        *x = mmul(*x, ninv);
    }
}

/// root of order n (n | 2^27): generator 31, p - 1 = 2^27 * 15
fn root_of_order(n: u64) -> u32 {
    let g = to_m(31);
    let w = mpow(g, (P64 - 1) / n);
    assert_eq!(from_m(mpow(w, n)), 1, "root order");
    assert_eq!(from_m(mpow(w, n / 2)), P - 1, "half-order = -1");
    w
}

fn main() {
    assert_eq!(P.wrapping_mul(NP), u32::MAX, "np const");
    for k in [3u64, 4, 14, 20, 25, 27] {
        root_of_order(1 << k);
    }
    println!("gate: root orders + half-order=-1 verified for 2^3..2^27 (generator 31)");

    let mut rng = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        (rng % P64) as u32
    };

    // gate: naive DFT cross-check at n=8 (in Montgomery domain)
    {
        let n = 8usize;
        let w = root_of_order(n as u64);
        let a: Vec<u32> = (0..n).map(|_| to_m(next())).collect();
        let mut fast = a.clone();
        ntt(&mut fast, w);
        for j in 0..n {
            let mut s = 0u32;
            for (i, &ai) in a.iter().enumerate() {
                s = badd(s, mmul(ai, mpow(w, (i * j) as u64)));
            }
            assert_eq!(s, fast[j], "DFT mismatch at {j}");
        }
        println!("gate: NTT == naive DFT at n=8");
    }
    // gate: round-trip at n=2^16
    {
        let n = 1usize << 16;
        let w = root_of_order(n as u64);
        let a: Vec<u32> = (0..n).map(|_| to_m(next())).collect();
        let mut b = a.clone();
        ntt(&mut b, w);
        intt(&mut b, w);
        assert_eq!(a, b, "round-trip");
        println!("gate: forward+inverse round-trip identity at n=2^16");
    }
    // gate: polynomial product vs schoolbook at n=16
    {
        let n = 16usize;
        let w = root_of_order(n as u64);
        let f: Vec<u32> = (0..8).map(|_| next()).collect();
        let g: Vec<u32> = (0..8).map(|_| next()).collect();
        let mut fa: Vec<u32> = f.iter().map(|&x| to_m(x)).collect();
        fa.resize(n, 0);
        let mut ga: Vec<u32> = g.iter().map(|&x| to_m(x)).collect();
        ga.resize(n, 0);
        ntt(&mut fa, w);
        ntt(&mut ga, w);
        let mut h: Vec<u32> = fa.iter().zip(&ga).map(|(x, y)| mmul(*x, *y)).collect();
        intt(&mut h, w);
        for k in 0..15 {
            let mut s = 0u64;
            for i in 0..=k.min(7) {
                if k - i < 8 {
                    s = (s + f[i] as u64 * g[k - i] as u64) % P64;
                }
            }
            assert_eq!(s as u32, from_m(h[k]), "conv mismatch at {k}");
        }
        println!("gate: NTT polynomial product == schoolbook at n=16");
    }

    let maxk: u32 = std::env::args()
        .nth(1)
        .and_then(|v| v.parse().ok())
        .unwrap_or(25);
    println!("BabyBear NTT timing (forward/inverse, seconds)");
    for k in 14..=maxk {
        let n = 1usize << k;
        let w = root_of_order(n as u64);
        let mut a: Vec<u32> = (0..n).map(|_| to_m(next())).collect();
        let reps = (1usize << 22).wrapping_shr(k).max(1);
        let t0 = std::time::Instant::now();
        for _ in 0..reps {
            ntt(&mut a, w);
        }
        let tf = t0.elapsed().as_secs_f64() / reps as f64;
        let t1 = std::time::Instant::now();
        for _ in 0..reps {
            intt(&mut a, w);
        }
        let ti = t1.elapsed().as_secs_f64() / reps as f64;
        println!("domain 2^{k} ({n}): fwd {tf:.4}  inv {ti:.4}");
    }
}
