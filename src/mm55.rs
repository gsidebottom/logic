//! A 55-addition, 23-multiplication algorithm for 3×3 matrix
//! multiplication (de Groote class `i19w225c4efh`) — fewer additions
//! than any previously published rank-23 scheme (the prior record was
//! 56, Sun 2026).  This is a faithful transcription of
//! `matmul/external/i19-55adds-slp.txt`: 23 multiplications, 55
//! binary additions/subtractions, negation free, no change of basis.
//!
//! It multiplies over **any ring** — every product keeps its left and
//! right factor in order — so it is a genuine bilinear algorithm and
//! applies recursively to block matrices.  The tests below check it
//! against the obvious 27-multiplication triple loop on random
//! integers *and* on random non-commutative 2×2-matrix entries, and
//! an operation counter proves it uses exactly 23 `*` and 55 `±`.
//!
//! Matrices are row-major length-9 arrays: index `3*i + j` is entry
//! (row i, col j), i,j ∈ {0,1,2}.

use std::ops::{Add, Mul, Neg, Sub};

/// A (not necessarily commutative) ring: the algorithm needs only
/// `+`, `−`, unary `−`, and an order-preserving `*`.
pub trait Ring:
    Copy
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + Neg<Output = Self>
{
}
impl Ring for i64 {}

/// C = A · B with 23 multiplications and 55 additions/subtractions.
pub fn matmul55<T: Ring>(a: &[T; 9], b: &[T; 9]) -> [T; 9] {
    let (a11, a12, a13) = (a[0], a[1], a[2]);
    let (a21, a22, a23) = (a[3], a[4], a[5]);
    let (a31, a32, a33) = (a[6], a[7], a[8]);
    let (b11, b12, b13) = (b[0], b[1], b[2]);
    let (b21, b22, b23) = (b[3], b[4], b[5]);
    let (b31, b32, b33) = (b[6], b[7], b[8]);

    // left factors P_i — 13 additions
    let aw0 = a13 - a23;
    let aw1 = a11 - aw0;
    let aw2 = a12 + aw1;
    let aw3 = aw2 - a23;
    let aw4 = aw2 - a22;
    let aw5 = a33 + aw3;
    let aw6 = aw5 - a12;
    let aw7 = aw4 - a21;
    let aw8 = a31 + aw7;
    let aw9 = a32 + aw8;
    let aw10 = aw5 - a32;
    let aw11 = a21 - a31;
    let aw12 = aw1 - aw11;

    // right factors Q_i — 14 additions
    let bw0 = b13 + b33;
    let bw1 = b11 + b31;
    let bw2 = b11 - b21;
    let bw3 = b11 + b13;
    let bw4 = b23 + b33;
    let bw5 = b13 + bw2;
    let bw6 = bw2 - bw4;
    let bw7 = bw5 - b23;
    let bw8 = b32 + bw1;
    let bw9 = b12 + bw8;
    let bw10 = bw8 - bw6;
    let bw11 = b22 + bw10;
    let bw12 = bw10 - b21;
    let bw13 = bw12 - b23;

    // 23 multiplications  M_i = P_i · Q_i  (left factor stays on the left)
    let m1 = aw2 * bw10;
    let m2 = aw8 * bw5;
    let m3 = a11 * bw0;
    let m4 = a32 * b22;
    let m5 = a11 * bw9;
    let m6 = aw6 * bw4;
    let m7 = aw10 * b23;
    let m8 = a33 * b31;
    let m9 = aw9 * b21;
    let m10 = aw1 * bw6;
    let m11 = a33 * b32;
    let m12 = aw3 * bw13;
    let m13 = a23 * b32;
    let m14 = aw7 * bw3;
    let m15 = a21 * b12;
    let m16 = a31 * b12;
    let m17 = a31 * b13;
    let m18 = aw0 * bw1;
    let m19 = aw5 * bw12;
    let m20 = aw12 * bw2;
    let m21 = a12 * bw11;
    let m22 = a22 * b22;
    let m23 = aw4 * bw7;

    // outputs C_ij — 28 additions (unary − is free)
    let cw0 = m6 - m19;
    let cw1 = cw0 + m11;
    let cw2 = m8 + cw1;
    let cw3 = -(m12 + cw2);
    let cw4 = -(m17 + cw3);
    let cw5 = m2 + cw4;
    let cw6 = m1 - m13;
    let cw7 = cw6 + m10;
    let cw8 = -(m14 + m12);
    let cw9 = cw8 + cw5;
    let cw10 = m18 + cw7;
    let cw11 = cw2 + cw10;
    let cw12 = m5 + m21;
    let cw13 = cw12 - cw10;
    let cw14 = m3 + cw3;
    let cw15 = cw7 - m20;
    let cw16 = cw15 + cw9;
    let cw17 = m15 + m22;
    let cw18 = cw17 + m13;
    let cw19 = m23 - cw5;
    let cw20 = cw19 - m10;
    let cw21 = cw20 + m20;
    let cw22 = m9 - cw1;
    let cw23 = cw22 + cw9;
    let cw24 = m4 + m16;
    let cw25 = cw24 + m11;
    let cw26 = m6 - m7;
    let cw27 = cw26 - cw4;

    [cw11, cw13, cw14, cw16, cw18, cw21, cw23, cw25, cw27]
}

/// The obvious definition: C_ij = Σ_k A_ik B_kj — 27 multiplications.
pub fn naive27<T: Ring>(a: &[T; 9], b: &[T; 9]) -> [T; 9] {
    std::array::from_fn(|idx| {
        let (i, j) = (idx / 3, idx % 3);
        a[3 * i] * b[j] + a[3 * i + 1] * b[3 + j] + a[3 * i + 2] * b[6 + j]
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::cell::Cell;

    // deterministic PRNG for the fuzz loop
    fn next(s: &mut u64) -> i64 {
        *s ^= *s << 13;
        *s ^= *s >> 7;
        *s ^= *s << 17;
        (*s >> 33) as i64 % 2001 - 1000 // in [-1000, 1000]
    }

    #[test]
    fn fuzz_scalars_vs_naive27() {
        let mut s = 0x1234_5678_9abc_def0u64;
        for _ in 0..500_000 {
            let a: [i64; 9] = std::array::from_fn(|_| next(&mut s));
            let b: [i64; 9] = std::array::from_fn(|_| next(&mut s));
            assert_eq!(matmul55(&a, &b), naive27(&a, &b));
        }
    }

    // ---- a non-commutative ring: 2×2 integer matrices ----
    #[derive(Clone, Copy, PartialEq, Debug)]
    struct M2([i64; 4]); // row-major 2×2

    impl Add for M2 {
        type Output = M2;
        fn add(self, o: M2) -> M2 {
            M2(std::array::from_fn(|i| self.0[i] + o.0[i]))
        }
    }
    impl Sub for M2 {
        type Output = M2;
        fn sub(self, o: M2) -> M2 {
            M2(std::array::from_fn(|i| self.0[i] - o.0[i]))
        }
    }
    impl Neg for M2 {
        type Output = M2;
        fn neg(self) -> M2 {
            M2(std::array::from_fn(|i| -self.0[i]))
        }
    }
    impl Mul for M2 {
        type Output = M2;
        fn mul(self, o: M2) -> M2 {
            let (a, b) = (self.0, o.0);
            M2([
                a[0] * b[0] + a[1] * b[2],
                a[0] * b[1] + a[1] * b[3],
                a[2] * b[0] + a[3] * b[2],
                a[2] * b[1] + a[3] * b[3],
            ])
        }
    }
    impl Ring for M2 {}

    #[test]
    fn fuzz_noncommutative_2x2_blocks() {
        // entries are 2×2 matrices -> this multiplies 6×6 matrices in
        // 3×3 blocks; passing proves the algorithm never uses ab = ba.
        let mut s = 0x0fee_1dad_cafe_babeu64;
        for _ in 0..50_000 {
            let a: [M2; 9] =
                std::array::from_fn(|_| M2(std::array::from_fn(|_| next(&mut s))));
            let b: [M2; 9] =
                std::array::from_fn(|_| M2(std::array::from_fn(|_| next(&mut s))));
            assert_eq!(matmul55(&a, &b), naive27(&a, &b));
        }
    }

    // ---- a ring that counts operations ----
    thread_local! {
        static ADDS: Cell<u64> = const { Cell::new(0) };
        static MULS: Cell<u64> = const { Cell::new(0) };
    }
    #[derive(Clone, Copy)]
    struct Counted(i64);
    impl Add for Counted {
        type Output = Counted;
        fn add(self, o: Counted) -> Counted {
            ADDS.with(|c| c.set(c.get() + 1));
            Counted(self.0 + o.0)
        }
    }
    impl Sub for Counted {
        type Output = Counted;
        fn sub(self, o: Counted) -> Counted {
            ADDS.with(|c| c.set(c.get() + 1));
            Counted(self.0 - o.0)
        }
    }
    impl Neg for Counted {
        type Output = Counted;
        fn neg(self) -> Counted {
            Counted(-self.0) // unary negation is free (not counted)
        }
    }
    impl Mul for Counted {
        type Output = Counted;
        fn mul(self, o: Counted) -> Counted {
            MULS.with(|c| c.set(c.get() + 1));
            Counted(self.0 * o.0)
        }
    }
    impl Ring for Counted {}

    #[test]
    fn exact_operation_counts_23_mul_55_add() {
        ADDS.with(|c| c.set(0));
        MULS.with(|c| c.set(0));
        let a: [Counted; 9] = std::array::from_fn(|i| Counted(i as i64 + 1));
        let b: [Counted; 9] = std::array::from_fn(|i| Counted(i as i64 - 4));
        let _ = matmul55(&a, &b);
        assert_eq!(MULS.with(|c| c.get()), 23, "multiplications");
        assert_eq!(ADDS.with(|c| c.get()), 55, "additions/subtractions");
    }
}
