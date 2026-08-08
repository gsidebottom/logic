//! memchip — Phase 1 regression gate for the two-stage prover fork
//! (task #32): the forked prover/verifier must be behavior-identical
//! to upstream uni-stark where no stage-2 exists. Cross-gates: fork
//! proof -> upstream verify AND upstream proof -> fork verify, plus
//! tamper rejection on both.
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
use p3_uni_stark::{StarkConfig, prove as up_prove, verify as up_verify};
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};

use benchair::ts_folder::TwoStageBuilder;
use benchair::ts_prover::{prove as ts_prove, prove_two_stage};
use benchair::ts_verifier::{verify as ts_verify, verify_two_stage};
use p3_field::BasedVectorSpace;
use p3_matrix::Matrix;

struct MulAir;
impl<F> BaseAir<F> for MulAir {
    fn width(&self) -> usize {
        3
    }
}
impl<AB: AirBuilder> Air<AB> for MulAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let row = main.current_slice();
        builder.assert_zero(row[0].into() * row[1].into() - row[2].into());
    }
}

fn trace(rows: usize, tamper: bool) -> RowMajorMatrix<BabyBear> {
    let mut rng = SmallRng::seed_from_u64(5);
    let mut v = BabyBear::zero_vec(rows * 3);
    for r in 0..rows {
        let a: BabyBear = rng.random();
        let b: BabyBear = rng.random();
        v[3 * r] = a;
        v[3 * r + 1] = b;
        v[3 * r + 2] = a * b;
    }
    if tamper {
        v[2] += BabyBear::ONE;
    }
    RowMajorMatrix::new(v, 3)
}

/// Minimal two-stage AIR: one main column v; stage-2 ext columns
/// inv = 1/(z - v) (witnessed inverse against the sampled challenge)
/// and acc = running sum of inv — the LogUp skeleton.
struct LogUpTestAir;
impl<F> BaseAir<F> for LogUpTestAir {
    fn width(&self) -> usize {
        1
    }
}
impl<AB: TwoStageBuilder> Air<AB> for LogUpTestAir {
    fn eval(&self, builder: &mut AB) {
        let v = builder.main().current(0).unwrap();
        let z = builder.ts_challenge(0);
        let inv = builder.perm_local_ext(0);
        let acc = builder.perm_local_ext(1);
        let inv_next = builder.perm_next_ext(0);
        let acc_next = builder.perm_next_ext(1);
        // inverse witness: inv * (z - v) == 1
        builder.assert_zero_ext(inv * (z - v.into()) - AB::ExprEF::ONE);
        // first row: acc == inv
        let first = builder.is_first_row();
        builder.assert_zero_ext(
            (acc.clone() - builder.perm_local_ext(0)) * first,
        );
        // transition: acc' == acc + inv'
        let trans = builder.is_transition();
        builder.assert_zero_ext(
            (acc_next - acc - inv_next) * trans,
        );
    }
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
    let config = MyConfig::new(pcs, challenger);

    let t = trace(1 << 10, false);
    let p_fork = ts_prove(&config, &MulAir, t.clone(), &[]);
    ts_verify(&config, &MulAir, &p_fork, &[]).expect("fork->fork verify");
    up_verify(&config, &MulAir, &p_fork, &[]).expect("fork->upstream verify");
    let p_up = up_prove(&config, &MulAir, t, &[]);
    ts_verify(&config, &MulAir, &p_up, &[]).expect("upstream->fork verify");
    println!("gate: fork proof == upstream-acceptable, both directions");

    let bad = trace(1 << 10, true);
    let pb = ts_prove(&config, &MulAir, bad, &[]);
    assert!(ts_verify(&config, &MulAir, &pb, &[]).is_err(), "fork accepted tamper");
    assert!(up_verify(&config, &MulAir, &pb, &[]).is_err(), "upstream accepted tamper");
    println!("gate: tampered trace rejected by both verifiers");
    println!("PHASE 1 COMPLETE: two-stage fork is behavior-identical with empty stage-2");

    // ---- Phase 2 gates: real stage-2 round end-to-end ----
    let rows = 1usize << 10;
    let mut rng2 = SmallRng::seed_from_u64(9);
    let vs: Vec<Val> = (0..rows).map(|_| rng2.random()).collect();
    let d = <Challenge as BasedVectorSpace<Val>>::DIMENSION;
    let vs_cl = vs.clone();
    let builder = move |chs: &[Challenge]| -> RowMajorMatrix<Val> {
        let z = chs[0];
        let mut m = Val::zero_vec(vs_cl.len() * 2 * d);
        let mut acc = Challenge::ZERO;
        for (r, &v) in vs_cl.iter().enumerate() {
            let inv = (z - v).inverse();
            acc += inv;
            for k in 0..d {
                m[r * 2 * d + k] = inv.as_basis_coefficients_slice()[k];
                m[r * 2 * d + d + k] = acc.as_basis_coefficients_slice()[k];
            }
        }
        RowMajorMatrix::new(m, 2 * d)
    };
    let trace2 = RowMajorMatrix::new(vs.clone(), 1);
    let tsp = prove_two_stage(&config, &LogUpTestAir, trace2, &[], None, 1, &builder);
    verify_two_stage(&config, &LogUpTestAir, &tsp, &[], None)
        .expect("two-stage valid proof rejected");
    println!("gate: two-stage LogUp AIR proves and verifies (sample -> commit -> fold -> open)");

    // tamper the WITNESS: one bad inverse must be rejected
    let vs_bad = vs.clone();
    let bad_builder = move |chs: &[Challenge]| -> RowMajorMatrix<Val> {
        let z = chs[0];
        let mut m = Val::zero_vec(vs_bad.len() * 2 * d);
        let mut acc = Challenge::ZERO;
        for (r, &v) in vs_bad.iter().enumerate() {
            let mut inv = (z - v).inverse();
            if r == 7 {
                inv += Challenge::ONE; // forged inverse
            }
            acc += inv;
            for k in 0..d {
                m[r * 2 * d + k] = inv.as_basis_coefficients_slice()[k];
                m[r * 2 * d + d + k] = acc.as_basis_coefficients_slice()[k];
            }
        }
        RowMajorMatrix::new(m, 2 * d)
    };
    let trace3 = RowMajorMatrix::new(vs.clone(), 1);
    let tsp_bad = prove_two_stage(&config, &LogUpTestAir, trace3, &[], None, 1, &bad_builder);
    assert!(
        verify_two_stage(&config, &LogUpTestAir, &tsp_bad, &[], None).is_err(),
        "two-stage accepted forged inverse"
    );
    println!("gate: forged stage-2 inverse rejected");
    println!("PHASE 2 COMPLETE: sound sample-after-commit round, gated end-to-end");
}
