//! tilechip — Phase 3 of task #32: the tile-interface memory-argument
//! precompile chip. One AIR, two row bands per tile:
//!   compute band (rpt rows): the mul-schedule chip (one row per core
//!     multiplication; L/R/P wiring preprocessed) — and each of its
//!     first 48 rows carries ONE memory operation: rows 0..16 read
//!     a[i], 16..32 read b[i], 32..48 write c[i]. The operand cell is
//!     selected by a preprocessed one-hot (io_sel) over main columns
//!     0..48 (the replicated a|b|c cells).
//!   memory band (48 rows): the memory table — (addr, val, mult=1)
//!     for the tile's 32 inputs and 16 outputs.
//! Stage-2 (sound: challenges gamma, beta sampled after the main
//! commit): per row an ext `term` witnessing
//!     term * (gamma + addr + beta*val) = is_mem*mult - is_io
//! and a running ext `acc`; the LAST-row constraint acc == 0 is the
//! LogUp balance = memory consistency. Naive packs H/112 tiles,
//! rank-48 packs H/96: predicted dilution 1.333x -> 1.167x.
use std::time::Instant;

use benchair::ts_folder::TwoStageBuilder;
use benchair::ts_prover::prove_two_stage;
use benchair::ts_verifier::verify_two_stage;
use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
use p3_challenger::DuplexChallenger;
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{BasedVectorSpace, Field, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use benchair::ts_prover::ts_setup_preprocessed as setup_preprocessed;
use p3_uni_stark::StarkConfig;
use rand::rngs::SmallRng;
use rand::{RngExt, SeedableRng};

mod mats {
    include!("../mats284.rs");
}

type BB = BabyBear;
type Challenge = BinomialExtensionField<BB, 4>;

// main columns
const CA: usize = 0; // a[16] | b[16] | c[16] = cells 0..48
const CLA: usize = 48;
const CRB: usize = 49;
const CPROD: usize = 50;
const CACC: usize = 51; // acc[16]
const CMVAL: usize = 67; // memory-band value
const CMULT: usize = 68; // memory-band multiplicity
const W: usize = 69;
// preprocessed columns
const PL: usize = 0;
const PR: usize = 16;
const PP: usize = 32;
const PSTART: usize = 48;
const PEND: usize = 49;
const PACT: usize = 50; // compute row
const PGMID: usize = 51;
const PADDR: usize = 52;
const PISMEM: usize = 53;
const PISIO: usize = 54;
const PIOSEL: usize = 55; // io_sel[48]
const PW: usize = 103;

fn coef(n: i32, d: u32) -> BB {
    let mag = BB::from_usize(n.unsigned_abs() as usize);
    let v = if n < 0 { -mag } else { mag };
    v * BB::from_usize(d as usize).inverse()
}

struct Schedule {
    l: Vec<[BB; 16]>,
    r: Vec<[BB; 16]>,
    p: Vec<[BB; 16]>,
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
    let mut p = vec![[BB::ZERO; 16]; 48];
    for z in 0..16 {
        for t in 0..48 {
            let (n, d) = mats::P284[z][t];
            p[t][z] = coef(n, d);
        }
    }
    Schedule { l, r, p }
}

struct TileChipAir {
    sched: Schedule,
    height: usize,
}

impl TileChipAir {
    fn rpt(&self) -> usize {
        self.sched.l.len()
    }
    fn rows_per_tile(&self) -> usize {
        self.rpt() + 48
    }
    fn tiles(&self) -> usize {
        self.height / self.rows_per_tile()
    }
}

impl<F: PrimeCharacteristicRing + From<BB> + Send + Sync> BaseAir<F> for TileChipAir {
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
        for tile in 0..tiles {
            let base_addr = tile * 48;
            for local in 0..self.rows_per_tile() {
                let row = tile * self.rows_per_tile() + local;
                let b = row * PW;
                if local < rpt {
                    // compute band
                    for i in 0..16 {
                        v[b + PL + i] = self.sched.l[local][i].into();
                        v[b + PR + i] = self.sched.r[local][i].into();
                        v[b + PP + i] = self.sched.p[local][i].into();
                    }
                    v[b + PSTART] = if local == 0 { F::ONE } else { F::ZERO };
                    v[b + PEND] = if local == rpt - 1 { F::ONE } else { F::ZERO };
                    v[b + PACT] = F::ONE;
                    v[b + PGMID] = if local > 0 { F::ONE } else { F::ZERO };
                    if local < 48 {
                        v[b + PISIO] = F::ONE;
                        v[b + PADDR] = F::from_usize(base_addr + local);
                        v[b + PIOSEL + local] = F::ONE;
                    }
                } else {
                    // memory band: one row per address
                    let o = local - rpt;
                    v[b + PISMEM] = F::ONE;
                    v[b + PADDR] = F::from_usize(base_addr + o);
                }
            }
        }
        Some(RowMajorMatrix::new(v, PW))
    }
}

impl<AB: TwoStageBuilder> Air<AB> for TileChipAir
where
    AB::F: From<BB> + Send + Sync,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let pl: Vec<AB::Expr> = prep.current_slice().iter().map(|x| (*x).into()).collect();
        let pn: Vec<AB::Expr> = prep.next_slice().iter().map(|x| (*x).into()).collect();
        let main = builder.main();
        let ml: Vec<AB::Expr> = main.current_slice().iter().map(|x| (*x).into()).collect();
        let mn: Vec<AB::Expr> = main.next_slice().iter().map(|x| (*x).into()).collect();

        // ---- schedule constraints (as in the mul-schedule AIR) ----
        let mut lsum = AB::Expr::ZERO;
        let mut rsum = AB::Expr::ZERO;
        for i in 0..16 {
            lsum = lsum + pl[PL + i].clone() * ml[CA + i].clone();
            rsum = rsum + pl[PR + i].clone() * ml[CA + 16 + i].clone();
        }
        builder.assert_zero(pl[PACT].clone() * (ml[CLA].clone() - lsum));
        builder.assert_zero(pl[PACT].clone() * (ml[CRB].clone() - rsum));
        builder.assert_zero(
            pl[PACT].clone() * (ml[CPROD].clone() - ml[CLA].clone() * ml[CRB].clone()),
        );
        for z in 0..16 {
            builder.assert_zero(
                pl[PSTART].clone()
                    * (ml[CACC + z].clone() - pl[PP + z].clone() * ml[CPROD].clone()),
            );
            builder.when_transition().assert_zero(
                pn[PGMID].clone()
                    * (mn[CACC + z].clone()
                        - ml[CACC + z].clone()
                        - pn[PP + z].clone() * mn[CPROD].clone()),
            );
            builder.assert_zero(
                pl[PEND].clone() * (ml[CACC + z].clone() - ml[CA + 32 + z].clone()),
            );
        }
        for i in 0..48 {
            builder
                .when_transition()
                .assert_zero(pn[PGMID].clone() * (mn[CA + i].clone() - ml[CA + i].clone()));
        }

        // ---- memory argument (stage 2) ----
        // VAL = is_mem*mval + sum_j io_sel_j * cell_j
        let mut val = pl[PISMEM].clone() * ml[CMVAL].clone();
        for j in 0..48 {
            val = val + pl[PIOSEL + j].clone() * ml[CA + j].clone();
        }
        let gamma = builder.ts_challenge(0);
        let beta = builder.ts_challenge(1);
        let term = builder.perm_local_ext(0);
        let acc = builder.perm_local_ext(1);
        let term_next = builder.perm_next_ext(0);
        let acc_next = builder.perm_next_ext(1);
        // fingerprint f = gamma + addr + beta*val  (ext, degree 2)
        let f = gamma + beta * val + pl[PADDR].clone();
        // signed multiplicity: memory rows emit +mult, io rows consume 1
        let signed =
            AB::ExprEF::ZERO + (pl[PISMEM].clone() * ml[CMULT].clone() - pl[PISIO].clone());
        // term witnesses signed/f  (degree 3)
        builder.assert_zero_ext(term.clone() * f - signed);
        // acc chains: first row acc == term; else acc' == acc + term'
        let first = builder.is_first_row();
        builder.assert_zero_ext((acc.clone() - term) * first);
        let trans = builder.is_transition();
        builder.assert_zero_ext((acc_next - acc.clone() - term_next) * trans);
        // LogUp balance: the final accumulator must vanish
        let last = builder.is_last_row();
        builder.assert_zero_ext(acc * last);
    }
}

/// Tamper selector for the gate suite.
#[derive(Clone, Copy, PartialEq)]
enum Tamper {
    None,
    MemoryValue,   // corrupt a memory-band value
    ComputeRead,   // compute band uses a value != memory (replicated cell)
    Multiplicity,  // a memory row claims mult = 2
    OutputWrite,   // corrupt the claimed output cell
}

fn make_main(air: &TileChipAir, tamper: Tamper) -> RowMajorMatrix<BB> {
    let rpt = air.rpt();
    let tiles = air.tiles();
    let mut rng = SmallRng::seed_from_u64(21);
    let mut v = BB::zero_vec(air.height * W);
    for tile in 0..tiles {
        let mut cells = [BB::ZERO; 48];
        for i in 0..32 {
            cells[i] = rng.random();
        }
        for i in 0..4 {
            for j in 0..4 {
                let mut s = BB::ZERO;
                for k in 0..4 {
                    s += cells[4 * i + k] * cells[16 + 4 * k + j];
                }
                cells[32 + 4 * i + j] = s;
            }
        }
        // memory band holds the TRUE image; tampers hit specific spots
        let mut mem = cells;
        let mut comp = cells;
        if tile == 0 {
            match tamper {
                Tamper::MemoryValue => mem[3] += BB::ONE,
                Tamper::ComputeRead => comp[5] += BB::ONE,
                Tamper::OutputWrite => comp[34] += BB::ONE,
                _ => {}
            }
        }
        let mut acc = [BB::ZERO; 16];
        for local in 0..air.rows_per_tile() {
            let row = tile * air.rows_per_tile() + local;
            let b = row * W;
            if local < rpt {
                let mut la = BB::ZERO;
                let mut rb = BB::ZERO;
                for i in 0..16 {
                    v[b + CA + i] = comp[i];
                    v[b + CA + 16 + i] = comp[16 + i];
                    v[b + CA + 32 + i] = comp[32 + i];
                    la += air.sched.l[local][i] * comp[i];
                    rb += air.sched.r[local][i] * comp[16 + i];
                }
                let prod = la * rb;
                v[b + CLA] = la;
                v[b + CRB] = rb;
                v[b + CPROD] = prod;
                for z in 0..16 {
                    acc[z] += air.sched.p[local][z] * prod;
                    v[b + CACC + z] = acc[z];
                }
            } else {
                let o = local - rpt;
                v[b + CMVAL] = mem[o];
                v[b + CMULT] =
                    if tile == 0 && o == 9 && tamper == Tamper::Multiplicity {
                        BB::TWO
                    } else {
                        BB::ONE
                    };
            }
        }
    }
    RowMajorMatrix::new(v, W)
}

/// Stage-2 builder: honest LogUp columns for whatever main/prep say.
fn perm_builder(
    air: &TileChipAir,
    main: &RowMajorMatrix<BB>,
    prep: &RowMajorMatrix<BB>,
    chs: &[Challenge],
) -> RowMajorMatrix<BB> {
    let (gamma, beta) = (chs[0], chs[1]);
    let d = <Challenge as BasedVectorSpace<BB>>::DIMENSION;
    let h = air.height;
    let mut m = BB::zero_vec(h * 2 * d);
    let mut acc = Challenge::ZERO;
    for r in 0..h {
        let is_mem = prep.get(r, PISMEM).unwrap();
        let is_io = prep.get(r, PISIO).unwrap();
        let addr = prep.get(r, PADDR).unwrap();
        let mut val = is_mem * main.get(r, CMVAL).unwrap();
        for j in 0..48 {
            val += prep.get(r, PIOSEL + j).unwrap() * main.get(r, CA + j).unwrap();
        }
        let f = gamma + beta * val + addr;
        let signed = is_mem * main.get(r, CMULT).unwrap() - is_io;
        let term = if signed == BB::ZERO {
            Challenge::ZERO
        } else {
            f.inverse() * signed
        };
        acc += term;
        for k in 0..d {
            m[r * 2 * d + k] = term.as_basis_coefficients_slice()[k];
            m[r * 2 * d + d + k] = acc.as_basis_coefficients_slice()[k];
        }
    }
    RowMajorMatrix::new(m, 2 * d)
}

fn main() {
    type Val = BabyBear;
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

    // ---- gates at 2^12: honest accept + four tamper rejections ----
    {
        let config = mk_config();
        for (name, sched) in [("naive", naive_schedule()), ("rank48", rank48_schedule())] {
            let air = TileChipAir { sched, height: 1 << 12 };
            let prep_m: RowMajorMatrix<BB> =
                <TileChipAir as BaseAir<BB>>::preprocessed_trace(&air).unwrap();
            let (pd, vk) = setup_preprocessed(&config, &air, 12).expect("prep");
            for (label, tamper, expect_ok) in [
                ("honest", Tamper::None, true),
                ("memory-value", Tamper::MemoryValue, false),
                ("compute-read", Tamper::ComputeRead, false),
                ("multiplicity", Tamper::Multiplicity, false),
                ("output-write", Tamper::OutputWrite, false),
            ] {
                let mt = make_main(&air, tamper);
                let mt_cl = mt.clone();
                let air_ref = &air;
                let prep_ref = &prep_m;
                let bld = move |chs: &[Challenge]| perm_builder(air_ref, &mt_cl, prep_ref, chs);
                let tsp =
                    prove_two_stage(&config, &air, mt, &[], Some(&pd), 2, &bld);
                let res = verify_two_stage(&config, &air, &tsp, &[], Some(&vk));
                assert_eq!(
                    res.is_ok(),
                    expect_ok,
                    "[{name}] {label}: expected ok={expect_ok}, got {res:?}"
                );
                println!("gate [{name}] {label}: {}", if expect_ok { "accepted" } else { "rejected" });
            }
        }
    }

    // ---- Phase 4 measurement: equal trace height, tiles/second ----
    for log_h in [14usize, 16, 18] {
        let mut rates = Vec::new();
        for (name, sched) in [("naive", naive_schedule()), ("rank48", rank48_schedule())] {
            let config = mk_config();
            let air = TileChipAir { sched, height: 1 << log_h };
            let tiles = air.tiles();
            let prep_m: RowMajorMatrix<BB> =
                <TileChipAir as BaseAir<BB>>::preprocessed_trace(&air).unwrap();
            let (pd, vk) = setup_preprocessed(&config, &air, log_h).expect("prep");
            let mt = make_main(&air, Tamper::None);
            let mt_cl = mt.clone();
            let air_ref = &air;
            let prep_ref = &prep_m;
            let bld = move |chs: &[Challenge]| perm_builder(air_ref, &mt_cl, prep_ref, chs);
            let t0 = Instant::now();
            let tsp = prove_two_stage(&config, &air, mt, &[], Some(&pd), 2, &bld);
            let pt = t0.elapsed();
            let t1 = Instant::now();
            verify_two_stage(&config, &air, &tsp, &[], Some(&vk)).unwrap();
            let vt = t1.elapsed();
            let rate = tiles as f64 / pt.as_secs_f64();
            rates.push(rate);
            println!(
                "2^{log_h} rows  {name:<7} tiles {tiles:>5}  prove {pt:>9.3?}  verify {vt:>8.3?}  {rate:.0} tiles/s"
            );
        }
        println!(
            "        -> rank48/naive throughput {:.3}x (row-count prediction 112/96 = 1.167x)",
            rates[1] / rates[0]
        );
    }
}
