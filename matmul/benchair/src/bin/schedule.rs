//! schedule — the memory-mediated precompile measurement: one
//! parametric AIR, one row per MULTIPLICATION (operands replicated in
//! committed columns, all scheme wiring in preprocessed columns), so
//! naive and rank-48 become two preprocessed schedules of the same
//! 67-column AIR differing only in rows per tile: 64 vs 48. At equal
//! trace height the rank-48 schedule packs 4/3 as many tiles — if
//! rows are the prover currency, that becomes tiles/second.
//! Gates: (1) host-side Brent-style check that every tile's final
//! accumulator equals schoolbook C (verifies the 284 tables as a
//! scheme over BabyBear); (2) both schedules' proofs verify; (3) a
//! tampered output is rejected by both.
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
use p3_uni_stark::{
    StarkConfig, prove_with_preprocessed, setup_preprocessed, verify_with_preprocessed,
};
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};

mod mats {
    include!("../mats284.rs");
}

type BB = BabyBear;

// main columns
const CA: usize = 0; // a[16]
const CB: usize = 16; // b[16]
const CC: usize = 32; // c[16]
const CLA: usize = 48;
const CRB: usize = 49;
const CPROD: usize = 50;
const CACC: usize = 51; // acc[16]
const W: usize = 67;
// preprocessed columns
const PL: usize = 0; // L[16]
const PR: usize = 16; // R[16]
const PP: usize = 32; // P[16]
const PSTART: usize = 48;
const PEND: usize = 49;
const PACT: usize = 50;
const PGMID: usize = 51; // active && !start (gates transitions INTO this row)
const PW: usize = 52;

fn coef(n: i32, d: u32) -> BB {
    let mag = BB::from_usize(n.unsigned_abs() as usize);
    let v = if n < 0 { -mag } else { mag };
    v * BB::from_usize(d as usize).inverse()
}

/// per-row schedule tables: l/r select operands, p scatters into acc
struct Schedule {
    l: Vec<[BB; 16]>,
    r: Vec<[BB; 16]>,
    p: Vec<[BB; 16]>, // p[t][z]
}

fn naive_schedule() -> Schedule {
    let mut l = vec![[BB::ZERO; 16]; 64];
    let mut r = vec![[BB::ZERO; 16]; 64];
    let mut p = vec![[BB::ZERO; 16]; 64];
    for t in 0..64 {
        let (i, j, k) = (t / 16, (t / 4) % 4, t % 4);
        l[t][4 * i + k] = BB::ONE;
        r[t][4 * k + j] = BB::ONE;
        p[t][4 * i + j] = BB::ONE;
    }
    Schedule { l, r, p }
}

fn rank48_schedule() -> Schedule {
    let cv = |row: &[(i32, u32); 16]| {
        let mut out = [BB::ZERO; 16];
        for (i, &(n, d)) in row.iter().enumerate() {
            out[i] = coef(n, d);
        }
        out
    };
    let l: Vec<_> = mats::L284.iter().map(cv).collect();
    let r: Vec<_> = mats::R284.iter().map(cv).collect();
    // P is stored 16x48; transpose to per-row [t][z]
    let mut p = vec![[BB::ZERO; 16]; 48];
    for z in 0..16 {
        for t in 0..48 {
            let (n, d) = mats::P284[z][t];
            p[t][z] = coef(n, d);
        }
    }
    Schedule { l, r, p }
}

struct SchedAir {
    sched: Schedule,
    height: usize,
}

impl SchedAir {
    fn rpt(&self) -> usize {
        self.sched.l.len()
    }
    fn tiles(&self) -> usize {
        self.height / self.rpt()
    }
}

impl<F: PrimeCharacteristicRing + From<BB> + Send + Sync> BaseAir<F> for SchedAir {
    fn width(&self) -> usize {
        W
    }
    fn preprocessed_width(&self) -> usize {
        PW
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let rpt = self.rpt();
        let tiles = self.tiles();
        let mut v = F::zero_vec(self.height * PW);
        for row in 0..tiles * rpt {
            let t = row % rpt;
            let base = row * PW;
            for i in 0..16 {
                v[base + PL + i] = self.sched.l[t][i].into();
                v[base + PR + i] = self.sched.r[t][i].into();
                v[base + PP + i] = self.sched.p[t][i].into();
            }
            v[base + PSTART] = if t == 0 { F::ONE } else { F::ZERO };
            v[base + PEND] = if t == rpt - 1 { F::ONE } else { F::ZERO };
            v[base + PACT] = F::ONE;
            v[base + PGMID] = if t > 0 { F::ONE } else { F::ZERO };
        }
        Some(RowMajorMatrix::new(v, PW))
    }
}

impl<AB: AirBuilder> Air<AB> for SchedAir
where
    AB::F: From<BB> + Send,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let pl: Vec<AB::Expr> =
            prep.current_slice().iter().map(|x| (*x).into()).collect();
        let pn: Vec<AB::Expr> = prep.next_slice().iter().map(|x| (*x).into()).collect();
        let main = builder.main();
        let ml: Vec<AB::Expr> =
            main.current_slice().iter().map(|x| (*x).into()).collect();
        let mn: Vec<AB::Expr> = main.next_slice().iter().map(|x| (*x).into()).collect();
        // la / rb wiring (degree 3 with the activity gate)
        let mut lsum = AB::Expr::ZERO;
        let mut rsum = AB::Expr::ZERO;
        for i in 0..16 {
            lsum = lsum + pl[PL + i].clone() * ml[CA + i].clone();
            rsum = rsum + pl[PR + i].clone() * ml[CB + i].clone();
        }
        builder.assert_zero(pl[PACT].clone() * (ml[CLA].clone() - lsum));
        builder.assert_zero(pl[PACT].clone() * (ml[CRB].clone() - rsum));
        // prod = la * rb
        builder.assert_zero(
            pl[PACT].clone() * (ml[CPROD].clone() - ml[CLA].clone() * ml[CRB].clone()),
        );
        for z in 0..16 {
            // start rows initialize acc
            builder.assert_zero(
                pl[PSTART].clone()
                    * (ml[CACC + z].clone() - pl[PP + z].clone() * ml[CPROD].clone()),
            );
            // interior rows accumulate (gated on the NEXT row's g_mid)
            builder.when_transition().assert_zero(
                pn[PGMID].clone()
                    * (mn[CACC + z].clone()
                        - ml[CACC + z].clone()
                        - pn[PP + z].clone() * mn[CPROD].clone()),
            );
            // end rows expose the output
            builder.assert_zero(
                pl[PEND].clone() * (ml[CACC + z].clone() - ml[CC + z].clone()),
            );
        }
        // operand/output replication within a tile group
        for i in 0..48 {
            builder
                .when_transition()
                .assert_zero(pn[PGMID].clone() * (mn[i].clone() - ml[i].clone()));
        }
    }
}

/// build the main trace; asserts final acc == schoolbook C per tile
fn make_trace(air: &SchedAir, tamper: bool) -> RowMajorMatrix<BB> {
    let rpt = air.rpt();
    let tiles = air.tiles();
    let mut rng = SmallRng::seed_from_u64(11);
    let mut v = BB::zero_vec(air.height * W);
    for tile in 0..tiles {
        let mut a = [BB::ZERO; 16];
        let mut b = [BB::ZERO; 16];
        for i in 0..16 {
            a[i] = rng.random();
            b[i] = rng.random();
        }
        let mut c = [BB::ZERO; 16];
        for i in 0..4 {
            for j in 0..4 {
                let mut s = BB::ZERO;
                for k in 0..4 {
                    s += a[4 * i + k] * b[4 * k + j];
                }
                c[4 * i + j] = s;
            }
        }
        let mut acc = [BB::ZERO; 16];
        for t in 0..rpt {
            let row = tile * rpt + t;
            let base = row * W;
            let mut la = BB::ZERO;
            let mut rb = BB::ZERO;
            for i in 0..16 {
                v[base + CA + i] = a[i];
                v[base + CB + i] = b[i];
                v[base + CC + i] = c[i];
                la += air.sched.l[t][i] * a[i];
                rb += air.sched.r[t][i] * b[i];
            }
            let prod = la * rb;
            v[base + CLA] = la;
            v[base + CRB] = rb;
            v[base + CPROD] = prod;
            for z in 0..16 {
                acc[z] += air.sched.p[t][z] * prod;
                v[base + CACC + z] = acc[z];
            }
        }
        assert_eq!(acc, c, "schedule tables wrong: acc != schoolbook C");
    }
    if tamper {
        // corrupt one output cell on a tile's last row
        v[(rpt - 1) * W + CC] += BB::ONE;
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

    // ---- gates at 2^12 ----
    {
        let config = mk_config();
        for (name, sched) in [("naive", naive_schedule()), ("rank48", rank48_schedule())] {
            let air = SchedAir { sched, height: 1 << 12 };
            let trace = make_trace(&air, false); // includes acc==C assert
            let (pd, vk) = setup_preprocessed(&config, &air, 12).expect("prep");
            let proof = prove_with_preprocessed(&config, &air, trace, &[], Some(&pd));
            verify_with_preprocessed(&config, &air, &proof, &[], Some(&vk))
                .unwrap_or_else(|e| panic!("{name} valid proof rejected: {e:?}"));
            let bad = make_trace(&air, true);
            let pbad = prove_with_preprocessed(&config, &air, bad, &[], Some(&pd));
            assert!(
                verify_with_preprocessed(&config, &air, &pbad, &[], Some(&vk)).is_err(),
                "{name} accepted tampered output"
            );
            println!(
                "gate [{name}]: schedule tables == schoolbook per tile; honest accepted; tampered rejected"
            );
        }
    }

    // ---- measurement: equal trace height, tiles/second ----
    for log_h in [16usize, 18, 20] {
        let mut rates = Vec::new();
        for (name, sched) in [("naive", naive_schedule()), ("rank48", rank48_schedule())] {
            let config = mk_config();
            let air = SchedAir { sched, height: 1 << log_h };
            let tiles = air.tiles();
            let trace = make_trace(&air, false);
            let (pd, vk) = setup_preprocessed(&config, &air, log_h).expect("prep");
            let t0 = Instant::now();
            let proof = prove_with_preprocessed(&config, &air, trace, &[], Some(&pd));
            let pt = t0.elapsed();
            let t1 = Instant::now();
            verify_with_preprocessed(&config, &air, &proof, &[], Some(&vk)).unwrap();
            let vt = t1.elapsed();
            let rate = tiles as f64 / pt.as_secs_f64();
            rates.push(rate);
            println!(
                "2^{log_h} rows  {name:<7} tiles {tiles:>6}  prove {pt:>9.3?}  verify {vt:>8.3?}  {:.0} tiles/s",
                rate
            );
        }
        println!(
            "        -> rank48 packs {:.3}x the throughput at equal trace budget",
            rates[1] / rates[0]
        );
    }
}
