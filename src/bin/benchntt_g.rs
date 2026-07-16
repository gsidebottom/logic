//! benchntt_g — Goldilocks radix-2 NTT benchmark (the field-native
//! answer to benchzk's BN254-Fr NTT curve). Gates before timing:
//! root-order checks, inverse round-trip, naive-DFT cross-check at
//! n=8, and negacyclic-free polynomial-product check at n=16 vs
//! schoolbook convolution.
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
fn fsub(a: u64, b: u64) -> u64 {
    if a >= b { a - b } else { a.wrapping_sub(b).wrapping_add(P) }
}
fn fpow(mut b: u64, mut e: u64) -> u64 {
    let mut r = 1u64;
    while e > 0 {
        if e & 1 == 1 {
            r = fmul(r, b);
        }
        b = fmul(b, b);
        e >>= 1;
    }
    r
}
fn finv(a: u64) -> u64 {
    fpow(a, P - 2)
}

/// in-place iterative Cooley–Tukey, bit-reversed input ordering
fn ntt(a: &mut [u64], root: u64) {
    let n = a.len();
    let lg = n.trailing_zeros();
    // bit-reverse permute
    for i in 0..n {
        let j = (i as u32).reverse_bits() >> (32 - lg);
        if (j as usize) > i {
            a.swap(i, j as usize);
        }
    }
    let mut len = 2;
    while len <= n {
        let w_len = fpow(root, (n / len) as u64);
        for start in (0..n).step_by(len) {
            let mut w = 1u64;
            for k in 0..len / 2 {
                let u = a[start + k];
                let v = fmul(a[start + k + len / 2], w);
                a[start + k] = fadd(u, v);
                a[start + k + len / 2] = fsub(u, v);
                w = fmul(w, w_len);
            }
        }
        len <<= 1;
    }
}

fn intt(a: &mut [u64], root: u64) {
    let n = a.len() as u64;
    ntt(a, finv(root));
    let ninv = finv(n % P);
    for x in a.iter_mut() {
        *x = fmul(*x, ninv);
    }
}

/// 2^32-order root: g = 7 is a generator of F_p^* for Goldilocks
fn root_of_order(n: u64) -> u64 {
    let w = fpow(7, (P - 1) / n);
    assert_eq!(fpow(w, n), 1, "root order");
    assert_eq!(fpow(w, n / 2), P - 1, "half-order = -1");
    w
}

fn main() {
    // gate 1: root orders across the curve
    for k in [3u64, 4, 14, 20, 25] {
        root_of_order(1 << k);
    }
    println!("gate: root orders + half-order=-1 verified for 2^3..2^25");

    let mut rng = 0x9e37_79b9_7f4a_7c15u64;
    let mut next = move || {
        rng ^= rng << 13;
        rng ^= rng >> 7;
        rng ^= rng << 17;
        rng % P
    };

    // gate 2: naive DFT cross-check at n=8
    {
        let n = 8usize;
        let w = root_of_order(n as u64);
        let a: Vec<u64> = (0..n).map(|_| next()).collect();
        let mut fast = a.clone();
        ntt(&mut fast, w);
        for j in 0..n {
            let mut s = 0u64;
            for (i, &ai) in a.iter().enumerate() {
                s = fadd(s, fmul(ai, fpow(w, (i * j) as u64)));
            }
            assert_eq!(s, fast[j], "DFT mismatch at {j}");
        }
        println!("gate: NTT == naive DFT at n=8");
    }

    // gate 3: round-trip at n=2^16
    {
        let n = 1usize << 16;
        let w = root_of_order(n as u64);
        let a: Vec<u64> = (0..n).map(|_| next()).collect();
        let mut b = a.clone();
        ntt(&mut b, w);
        intt(&mut b, w);
        assert_eq!(a, b, "round-trip");
        println!("gate: forward+inverse round-trip identity at n=2^16");
    }

    // gate 4: polynomial product vs schoolbook at deg<8 (n=16)
    {
        let n = 16usize;
        let w = root_of_order(n as u64);
        let f: Vec<u64> = (0..8).map(|_| next()).collect();
        let g: Vec<u64> = (0..8).map(|_| next()).collect();
        let mut fa = f.clone();
        fa.resize(n, 0);
        let mut ga = g.clone();
        ga.resize(n, 0);
        ntt(&mut fa, w);
        ntt(&mut ga, w);
        let mut h: Vec<u64> = fa.iter().zip(&ga).map(|(x, y)| fmul(*x, *y)).collect();
        intt(&mut h, w);
        for k in 0..15 {
            let mut s = 0u64;
            for i in 0..=k.min(7) {
                if k - i < 8 {
                    s = fadd(s, fmul(f[i], g[k - i]));
                }
            }
            assert_eq!(s, h[k], "conv mismatch at {k}");
        }
        println!("gate: NTT polynomial product == schoolbook at n=16");
    }

    // timing curve
    let maxk: u32 = std::env::args()
        .nth(1)
        .and_then(|v| v.parse().ok())
        .unwrap_or(25);
    println!("Goldilocks NTT timing (forward/inverse, seconds)");
    for k in 14..=maxk {
        let n = 1usize << k;
        let w = root_of_order(n as u64);
        let mut a: Vec<u64> = (0..n).map(|_| next()).collect();
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
