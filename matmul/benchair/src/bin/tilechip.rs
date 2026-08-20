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
//!
//! Rosowski-46 variant (task: commutative schemes): 46 products from
//! Rosowski 2019 Thm 2 (verified in matmul/comm/rosowski.py). The
//! mixed A|B factors need lr_w = 32 linear forms; the io floor keeps
//! the tile at the same 96 rows (46 product rows + 2 io-only padding
//! rows), so the two saved products buy nothing and the doubled form
//! width is pure cost. MEASURED (2026-08-19): rosowski46/rank48 =
//! 0.95-0.98x at 2^14/16/18 — rank-48 bilinear is the optimum for
//! this 4x4 tile geometry. Details in matmul/comm/SUMMARY.md.
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
// preprocessed columns (offsets depend on the schedule's linear-form
// width lr_w: 16 = L reads a-cells / R reads b-cells (bilinear);
// 32 = L and R each read ALL of a|b (commutative mixed forms))
const PL: usize = 0;
#[inline]
fn pr_off(lr_w: usize) -> usize { lr_w }
#[inline]
fn pp_off(lr_w: usize) -> usize { 2 * lr_w }
#[inline]
fn pstart_off(lr_w: usize) -> usize { 2 * lr_w + 16 }
#[inline]
fn pend_off(lr_w: usize) -> usize { 2 * lr_w + 17 }
#[inline]
fn pact_off(lr_w: usize) -> usize { 2 * lr_w + 18 }
#[inline]
fn pgmid_off(lr_w: usize) -> usize { 2 * lr_w + 19 }
#[inline]
fn paddr_off(lr_w: usize) -> usize { 2 * lr_w + 20 }
#[inline]
fn pismem_off(lr_w: usize) -> usize { 2 * lr_w + 21 }
#[inline]
fn pisio_off(lr_w: usize) -> usize { 2 * lr_w + 22 }
#[inline]
fn piosel_off(lr_w: usize) -> usize { 2 * lr_w + 23 }
#[inline]
fn pw_of(lr_w: usize) -> usize { 2 * lr_w + 23 + 48 }

fn coef(n: i32, d: u32) -> BB {
    let mag = BB::from_usize(n.unsigned_abs() as usize);
    let v = if n < 0 { -mag } else { mag };
    v * BB::from_usize(d as usize).inverse()
}

struct Schedule {
    /// linear-form width: 16 (L over a, R over b) or 32 (both over a|b)
    lr_w: usize,
    l: Vec<Vec<BB>>,
    r: Vec<Vec<BB>>,
    p: Vec<[BB; 16]>,
}

fn naive_schedule() -> Schedule {
    let mut l = vec![vec![BB::ZERO; 16]; 64];
    let mut r = vec![vec![BB::ZERO; 16]; 64];
    let mut p = vec![[BB::ZERO; 16]; 64];
    for t in 0..64 {
        let (i, j, k) = (t / 16, (t / 4) % 4, t % 4);
        l[t][4 * i + k] = BB::ONE;
        r[t][4 * k + j] = BB::ONE;
        p[t][4 * i + j] = BB::ONE;
    }
    Schedule { lr_w: 16, l, r, p }
}

/// Rosowski 2019 Theorem 2 for <4,4,4>: 46 products over a COMMUTATIVE
/// ring (verified over Z and BabyBear in matmul/comm/rosowski.py).
/// Non-bilinear: factors mix a- and b-cells, so lr_w = 32 and each
/// L/R vector indexes the whole a|b block (a[i][j] = 4i+j,
/// b[i][j] = 16 + 4i+j). Product order: P1(i,k), P2(i,k), S(j,k),
/// Q(i,j,k) for i in 0..4, j in 1..4, k in 0..2.
fn rosowski46_schedule() -> Schedule {
    let a = |i: usize, j: usize| 4 * i + j;
    let b = |i: usize, j: usize| 16 + 4 * i + j;
    let mut l: Vec<Vec<BB>> = Vec::new();
    let mut r: Vec<Vec<BB>> = Vec::new();
    let mut p: Vec<[BB; 16]> = Vec::new();
    let mut push = |lv: Vec<(usize, i32)>, rv: Vec<(usize, i32)>, pv: Vec<(usize, i32)>| {
        let mut lrow = vec![BB::ZERO; 32];
        let mut rrow = vec![BB::ZERO; 32];
        let mut prow = [BB::ZERO; 16];
        let sc = |n: i32| if n < 0 { -BB::from_usize(n.unsigned_abs() as usize) } else { BB::from_usize(n as usize) };
        for (c, n) in lv { lrow[c] = sc(n); }
        for (c, n) in rv { rrow[c] = sc(n); }
        for (z, n) in pv { prow[z] = sc(n); }
        l.push(lrow); r.push(rrow); p.push(prow);
    };
    // P1(i,k) = a[i][2k] * (b[2k][0] + a[i][2k+1])
    //   feeds c[i][0] +1 and c[i][j] -1 for j=1..3
    for i in 0..4 {
        for k in 0..2 {
            push(vec![(a(i, 2 * k), 1)],
                 vec![(b(2 * k, 0), 1), (a(i, 2 * k + 1), 1)],
                 vec![(4 * i, 1), (4 * i + 1, -1), (4 * i + 2, -1), (4 * i + 3, -1)]);
        }
    }
    // P2(i,k) = a[i][2k+1] * (b[2k+1][0] - a[i][2k])  -> c[i][0] +1
    for i in 0..4 {
        for k in 0..2 {
            push(vec![(a(i, 2 * k + 1), 1)],
                 vec![(b(2 * k + 1, 0), 1), (a(i, 2 * k), -1)],
                 vec![(4 * i, 1)]);
        }
    }
    // S(j,k) = b[2k+1][j] * (b[2k][0] + b[2k][j])  -> c[i][j] -1 all i
    for j in 1..4 {
        for k in 0..2 {
            push(vec![(b(2 * k + 1, j), 1)],
                 vec![(b(2 * k, 0), 1), (b(2 * k, j), 1)],
                 (0..4).map(|i| (4 * i + j, -1)).collect());
        }
    }
    // Q(i,j,k) = (a[i][2k] + b[2k+1][j]) * (a[i][2k+1] + b[2k][0] + b[2k][j])
    //   -> c[i][j] +1
    for i in 0..4 {
        for j in 1..4 {
            for k in 0..2 {
                push(vec![(a(i, 2 * k), 1), (b(2 * k + 1, j), 1)],
                     vec![(a(i, 2 * k + 1), 1), (b(2 * k, 0), 1), (b(2 * k, j), 1)],
                     vec![(4 * i + j, 1)]);
            }
        }
    }
    assert_eq!(l.len(), 46);
    Schedule { lr_w: 32, l, r, p }
}

fn rank48_schedule() -> Schedule {
    let cv = |row: &[(i32, u32); 16]| {
        let mut out = [BB::ZERO; 16];
        for (i, &(n, d)) in row.iter().enumerate() {
            out[i] = coef(n, d);
        }
        out
    };
    let l: Vec<Vec<BB>> = mats::L284.iter().map(|r| cv(r).to_vec()).collect();
    let r: Vec<Vec<BB>> = mats::R284.iter().map(|x| cv(x).to_vec()).collect();
    let mut p = vec![[BB::ZERO; 16]; 48];
    for z in 0..16 {
        for t in 0..48 {
            let (n, d) = mats::P284[z][t];
            p[t][z] = coef(n, d);
        }
    }
    Schedule { lr_w: 16, l, r, p }
}

struct TileChipAir {
    sched: Schedule,
    height: usize,
}

impl TileChipAir {
    fn rpt(&self) -> usize {
        self.sched.l.len()
    }
    /// compute band: max(rpt, 48) rows — the 48 io ops ride one per row,
    /// so schemes under 48 products pad (rank<48 buys no rows here).
    fn cband(&self) -> usize {
        self.rpt().max(48)
    }
    fn rows_per_tile(&self) -> usize {
        self.cband() + 48
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
        pw_of(self.sched.lr_w)
    }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let rpt = self.rpt();
        let cband = self.cband();
        let lw = self.sched.lr_w;
        let pw = pw_of(lw);
        let tiles = self.tiles();
        let mut v = F::zero_vec(self.height * pw);
        for tile in 0..tiles {
            let base_addr = tile * 48;
            for local in 0..self.rows_per_tile() {
                let row = tile * self.rows_per_tile() + local;
                let b = row * pw;
                if local < cband {
                    // compute band (rows >= rpt are io-only padding)
                    if local < rpt {
                        for i in 0..lw {
                            v[b + PL + i] = self.sched.l[local][i].into();
                            v[b + pr_off(lw) + i] = self.sched.r[local][i].into();
                        }
                        for z in 0..16 {
                            v[b + pp_off(lw) + z] = self.sched.p[local][z].into();
                        }
                        v[b + pact_off(lw)] = F::ONE;
                        v[b + pend_off(lw)] =
                            if local == rpt - 1 { F::ONE } else { F::ZERO };
                    }
                    v[b + pstart_off(lw)] = if local == 0 { F::ONE } else { F::ZERO };
                    v[b + pgmid_off(lw)] = if local > 0 { F::ONE } else { F::ZERO };
                    if local < 48 {
                        v[b + pisio_off(lw)] = F::ONE;
                        v[b + paddr_off(lw)] = F::from_usize(base_addr + local);
                        v[b + piosel_off(lw) + local] = F::ONE;
                    }
                } else {
                    // memory band: one row per address
                    let o = local - cband;
                    v[b + pismem_off(lw)] = F::ONE;
                    v[b + paddr_off(lw)] = F::from_usize(base_addr + o);
                }
            }
        }
        Some(RowMajorMatrix::new(v, pw))
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
        // lr_w = 16: L over a-cells 0..16, R over b-cells 16..32.
        // lr_w = 32: L and R both over the whole a|b block 0..32
        //   (commutative mixed forms). Unified: R reads cells
        //   (32 - lr_w)..32.
        let lw = self.sched.lr_w;
        let roff = 32 - lw;
        let mut lsum = AB::Expr::ZERO;
        let mut rsum = AB::Expr::ZERO;
        for i in 0..lw {
            lsum = lsum + pl[PL + i].clone() * ml[CA + i].clone();
            rsum = rsum + pl[pr_off(lw) + i].clone() * ml[CA + roff + i].clone();
        }
        let pact = pact_off(lw);
        let pstart = pstart_off(lw);
        let pend = pend_off(lw);
        let pgmid = pgmid_off(lw);
        let pp = pp_off(lw);
        builder.assert_zero(pl[pact].clone() * (ml[CLA].clone() - lsum));
        builder.assert_zero(pl[pact].clone() * (ml[CRB].clone() - rsum));
        builder.assert_zero(
            pl[pact].clone() * (ml[CPROD].clone() - ml[CLA].clone() * ml[CRB].clone()),
        );
        for z in 0..16 {
            builder.assert_zero(
                pl[pstart].clone()
                    * (ml[CACC + z].clone() - pl[pp + z].clone() * ml[CPROD].clone()),
            );
            builder.when_transition().assert_zero(
                pn[pgmid].clone()
                    * (mn[CACC + z].clone()
                        - ml[CACC + z].clone()
                        - pn[pp + z].clone() * mn[CPROD].clone()),
            );
            builder.assert_zero(
                pl[pend].clone() * (ml[CACC + z].clone() - ml[CA + 32 + z].clone()),
            );
        }
        for i in 0..48 {
            builder
                .when_transition()
                .assert_zero(pn[pgmid].clone() * (mn[CA + i].clone() - ml[CA + i].clone()));
        }

        // ---- memory argument (stage 2) ----
        // VAL = is_mem*mval + sum_j io_sel_j * cell_j
        let mut val = pl[pismem_off(lw)].clone() * ml[CMVAL].clone();
        for j in 0..48 {
            val = val + pl[piosel_off(lw) + j].clone() * ml[CA + j].clone();
        }
        let gamma = builder.ts_challenge(0);
        let beta = builder.ts_challenge(1);
        let term = builder.perm_local_ext(0);
        let acc = builder.perm_local_ext(1);
        let term_next = builder.perm_next_ext(0);
        let acc_next = builder.perm_next_ext(1);
        // fingerprint f = gamma + addr + beta*val  (ext, degree 2)
        let f = gamma + beta * val + pl[paddr_off(lw)].clone();
        // signed multiplicity: memory rows emit +mult, io rows consume 1
        let signed = AB::ExprEF::ZERO
            + (pl[pismem_off(lw)].clone() * ml[CMULT].clone() - pl[pisio_off(lw)].clone());
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
    let cband = air.cband();
    let lw = air.sched.lr_w;
    let roff = 32 - lw;
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
            if local < cband {
                for i in 0..48 {
                    v[b + CA + i] = comp[i];
                }
                if local < rpt {
                    let mut la = BB::ZERO;
                    let mut rb = BB::ZERO;
                    for i in 0..lw {
                        la += air.sched.l[local][i] * comp[i];
                        rb += air.sched.r[local][i] * comp[roff + i];
                    }
                    let prod = la * rb;
                    v[b + CLA] = la;
                    v[b + CRB] = rb;
                    v[b + CPROD] = prod;
                    for z in 0..16 {
                        acc[z] += air.sched.p[local][z] * prod;
                    }
                }
                // io-only padding rows (rpt <= local < cband) carry acc
                for z in 0..16 {
                    v[b + CACC + z] = acc[z];
                }
            } else {
                let o = local - cband;
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
    let lw = air.sched.lr_w;
    let d = <Challenge as BasedVectorSpace<BB>>::DIMENSION;
    let h = air.height;
    let mut m = BB::zero_vec(h * 2 * d);
    let mut acc = Challenge::ZERO;
    for r in 0..h {
        let is_mem = prep.get(r, pismem_off(lw)).unwrap();
        let is_io = prep.get(r, pisio_off(lw)).unwrap();
        let addr = prep.get(r, paddr_off(lw)).unwrap();
        let mut val = is_mem * main.get(r, CMVAL).unwrap();
        for j in 0..48 {
            val += prep.get(r, piosel_off(lw) + j).unwrap() * main.get(r, CA + j).unwrap();
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

/// Gate: run the schedule on a random tile and check it reproduces the
/// naive 4x4 product. Independent of the AIR — catches formula
/// transcription errors with a clean message before any proving.
fn schedule_selfcheck(name: &str, sched: &Schedule) {
    let mut rng = SmallRng::seed_from_u64(7);
    for _ in 0..8 {
        let mut cells = [BB::ZERO; 32];
        for c in cells.iter_mut() {
            *c = rng.random();
        }
        let mut want = [BB::ZERO; 16];
        for i in 0..4 {
            for j in 0..4 {
                for k in 0..4 {
                    want[4 * i + j] += cells[4 * i + k] * cells[16 + 4 * k + j];
                }
            }
        }
        let roff = 32 - sched.lr_w;
        let mut got = [BB::ZERO; 16];
        for t in 0..sched.l.len() {
            let mut la = BB::ZERO;
            let mut rb = BB::ZERO;
            for i in 0..sched.lr_w {
                la += sched.l[t][i] * cells[i];
                rb += sched.r[t][i] * cells[roff + i];
            }
            for z in 0..16 {
                got[z] += sched.p[t][z] * la * rb;
            }
        }
        assert_eq!(got, want, "schedule {name} does not compute A*B");
    }
    println!(
        "selfcheck [{name}]: {} products, lr_w {}, reproduces A*B on 8 random tiles",
        sched.l.len(),
        sched.lr_w
    );
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

    for (name, sched) in [
        ("naive", naive_schedule()),
        ("rank48", rank48_schedule()),
        ("rosowski46", rosowski46_schedule()),
    ] {
        schedule_selfcheck(name, &sched);
    }

    // ---- gates at 2^12: honest accept + four tamper rejections ----
    {
        let config = mk_config();
        for (name, sched) in [
            ("naive", naive_schedule()),
            ("rank48", rank48_schedule()),
            ("rosowski46", rosowski46_schedule()),
        ] {
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
        for (name, sched) in [
            ("naive", naive_schedule()),
            ("rank48", rank48_schedule()),
            ("rosowski46", rosowski46_schedule()),
        ] {
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
        println!(
            "        -> rosowski46/rank48 throughput {:.3}x (equal 96-row geometry; \
             cost delta = 32-wide mixed forms + 32 extra preprocessed cols)",
            rates[2] / rates[1]
        );
    }
}
