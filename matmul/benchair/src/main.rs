//! benchair — PLONKish/AIR custom-gate port over BabyBear (Plonky3
//! uni-stark). Two AIRs over the IDENTICAL 48-column trace (16 A,
//! 16 B, 16 C cells per row; one 4x4 tile multiply per row), so
//! commitment cost is held constant and the measured difference is
//! purely the GATE:
//!   NaiveTileAir  — 16 constraints, C_ij = sum_k A_ik * B_kj
//!                   (64 in-constraint multiplies per row)
//!   Rank48TileAir — the 284-op accurate SLP evaluated over AIR
//!                   expressions (El implemented for the expression
//!                   type; slp284g.rs runs unchanged): 48 products of
//!                   two fixed linear forms, P-recombined; all linear
//!                   coefficients are constants — the R1CS density
//!                   tax structurally cannot appear.
//! Gates: verify() must accept both proofs and reject a tampered
//! trace for both AIRs; the two AIRs share one trace generator whose
//! C is computed independently (schoolbook, canonical arithmetic).
use std::time::Instant;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::{StarkConfig, prove, verify};
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};

// ---- the El trait the generated SLP modules are generic over ----
pub trait El: Clone {
    fn add(&self, o: &Self) -> Self;
    fn sub(&self, o: &Self) -> Self;
    fn neg(&self) -> Self;
    fn scale2(&self, k: i32) -> Self;
}

/// El over any expression-like algebra: carries the constant 1/2 so
/// negative dyadic scalings stay constant-coefficient (degree 0).
#[derive(Clone)]
struct Ex<E> {
    e: E,
    half: E,
}

impl<E> El for Ex<E>
where
    E: Clone
        + core::ops::Add<Output = E>
        + core::ops::Sub<Output = E>
        + core::ops::Neg<Output = E>
        + core::ops::Mul<Output = E>,
{
    fn add(&self, o: &Self) -> Self {
        Ex { e: self.e.clone() + o.e.clone(), half: self.half.clone() }
    }
    fn sub(&self, o: &Self) -> Self {
        Ex { e: self.e.clone() - o.e.clone(), half: self.half.clone() }
    }
    fn neg(&self) -> Self {
        Ex { e: -self.e.clone(), half: self.half.clone() }
    }
    fn scale2(&self, k: i32) -> Self {
        let mut v = self.e.clone();
        if k >= 0 {
            for _ in 0..k {
                v = v.clone() + v;
            }
        } else {
            for _ in 0..(-k) {
                v = v * self.half.clone();
            }
        }
        Ex { e: v, half: self.half.clone() }
    }
}

mod g284 {
    use super::El;
    include!("../../../src/slp284g.rs");
}

const W: usize = 48; // 16 A + 16 B + 16 C

struct NaiveTileAir;
impl<F> BaseAir<F> for NaiveTileAir {
    fn width(&self) -> usize {
        W
    }
}
impl<AB: AirBuilder> Air<AB> for NaiveTileAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let row = main.current_slice();
        for i in 0..4 {
            for j in 0..4 {
                let mut s: AB::Expr = row[i * 4].into() * row[16 + j].into();
                for k in 1..4 {
                    s = s + row[i * 4 + k].into() * row[16 + k * 4 + j].into();
                }
                builder.assert_eq(s, row[32 + i * 4 + j]);
            }
        }
    }
}

struct Rank48TileAir;
impl<F> BaseAir<F> for Rank48TileAir {
    fn width(&self) -> usize {
        W
    }
}
impl<AB: AirBuilder> Air<AB> for Rank48TileAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let row = main.current_slice();
        let half: AB::Expr = AB::Expr::ONE.halve();
        let wrap = |i: usize| Ex::<AB::Expr> {
            e: row[i].into(),
            half: half.clone(),
        };
        let a: Vec<Ex<AB::Expr>> = (0..16).map(wrap).collect();
        let b: Vec<Ex<AB::Expr>> = (16..32).map(wrap).collect();
        let zero = Ex::<AB::Expr> {
            e: AB::Expr::ZERO,
            half: half.clone(),
        };
        let mut la = vec![zero.clone(); 48];
        let mut rb = vec![zero.clone(); 48];
        g284::gslp_l(&a, &mut la);
        g284::gslp_r(&b, &mut rb);
        let pr: Vec<Ex<AB::Expr>> = (0..48)
            .map(|t| Ex {
                e: la[t].e.clone() * rb[t].e.clone(),
                half: half.clone(),
            })
            .collect();
        let mut c = vec![zero; 16];
        g284::gslp_p(&pr, &mut c);
        for z in 0..16 {
            builder.assert_eq(c[z].e.clone(), row[32 + z]);
        }
    }
}

/// one shared trace: T rows, each an independent random tile with C
/// computed by schoolbook (so both AIRs judge the same witness)
fn make_trace(rows: usize, tamper: bool) -> RowMajorMatrix<BabyBear> {
    let mut rng = SmallRng::seed_from_u64(7);
    let mut v = BabyBear::zero_vec(rows * W);
    for r in 0..rows {
        let base = r * W;
        for i in 0..32 {
            v[base + i] = rng.random();
        }
        for i in 0..4 {
            for j in 0..4 {
                let mut s = BabyBear::ZERO;
                for k in 0..4 {
                    s += v[base + i * 4 + k] * v[base + 16 + k * 4 + j];
                }
                v[base + 32 + i * 4 + j] = s;
            }
        }
    }
    if tamper {
        v[32] += BabyBear::ONE;
    }
    RowMajorMatrix::new(v, W)
}

fn main() {
    type Val = BabyBear;
    type Challenge = BinomialExtensionField<Val, 4>;
    type Perm = Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type ValMmcs =
        MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, MyHash, MyCompress, 2, 8>;
    type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
    type Dft = Radix2DitParallel<Val>;
    type Challenger = DuplexChallenger<Val, Perm, 16, 8>;
    type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
    type MyConfig = StarkConfig<Pcs, Challenge, Challenger>;

    let mk_config = || {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm.clone());
        let val_mmcs = ValMmcs::new(hash, compress, 0);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let fri_params = FriParameters {
            log_blowup: 1,
            log_final_poly_len: 3,
            max_log_arity: 2,
            num_queries: 100,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: 8,
            mmcs: challenge_mmcs,
        };
        let pcs = Pcs::new(Dft::default(), val_mmcs, fri_params);
        let challenger = Challenger::new(perm);
        MyConfig::new(pcs, challenger)
    };

    // ---- gates: accept valid, reject tampered, for BOTH airs ----
    {
        let config = mk_config();
        let t = make_trace(1 << 8, false);
        let p1 = prove(&config, &NaiveTileAir, t.clone(), &[]);
        verify(&config, &NaiveTileAir, &p1, &[]).expect("naive valid proof rejected");
        let p2 = prove(&config, &Rank48TileAir, t, &[]);
        verify(&config, &Rank48TileAir, &p2, &[]).expect("rank48 valid proof rejected");
        println!("gate: both AIRs accept the honest trace (2^8 tiles)");
        let bad = make_trace(1 << 8, true);
        let pb1 = prove(&config, &NaiveTileAir, bad.clone(), &[]);
        assert!(
            verify(&config, &NaiveTileAir, &pb1, &[]).is_err(),
            "naive accepted tampered trace"
        );
        let pb2 = prove(&config, &Rank48TileAir, bad, &[]);
        assert!(
            verify(&config, &Rank48TileAir, &pb2, &[]).is_err(),
            "rank48 accepted tampered trace"
        );
        println!("gate: both AIRs reject a tampered product");
    }

    // ---- timing ----
    for log_rows in [12usize, 14, 16] {
        let rows = 1usize << log_rows;
        let trace = make_trace(rows, false);
        for is48 in [false, true] {
            let name = if is48 { "rank48-gate" } else { "naive-gate" };
            let config = mk_config();
            let tr = trace.clone();
            let t0 = Instant::now();
            let (pt, vt) = if is48 {
                let proof = prove(&config, &Rank48TileAir, tr, &[]);
                let pt = t0.elapsed();
                let t1 = Instant::now();
                verify(&config, &Rank48TileAir, &proof, &[]).unwrap();
                (pt, t1.elapsed())
            } else {
                let proof = prove(&config, &NaiveTileAir, tr, &[]);
                let pt = t0.elapsed();
                let t1 = Instant::now();
                verify(&config, &NaiveTileAir, &proof, &[]).unwrap();
                (pt, t1.elapsed())
            };
            println!("2^{log_rows} tiles  {name:<12} prove {pt:>10.3?}  verify {vt:>9.3?}");
        }
    }
}
