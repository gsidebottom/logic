//! flip48p — the 4x4 flip engine over PRIME FIELDS: the
//! field-specific rank-47 hunt (see doc/matmul_zkml_paper.md §7).
//! Precedent: 4x4:47 exists mod 2 (AlphaTensor) with no known
//! characteristic-0 equal, so rank at 4x4 is genuinely
//! field-dependent — and nobody has searched the big proof fields.
//! A verified 47 over Goldilocks/BabyBear would beat the DPS-48
//! recursion base for zkML provers.
//!
//! Same shared engine as flip23p (src/flip23p_engine.rs), shape
//! consts DIM=4 / RANK0=48; seed = the DPS <4x4x4:48> LRP trio
//! (hal-05112145) in matmul/dps48 (dyadic fractions, exact mod p).
//!
//!   --prime goldilocks   p = 2^64 - 2^32 + 1   (default)
//!   --prime babybear     p = 2^31 - 2^27 + 1
//!   --prime m31          p = 2^31 - 1
//!
//! Modes: storm | --census | --native | --lams | --pursue7 |
//! --pursue8 | --repair K   (see the engine header).

mod goldilocks {
    pub const DIM: usize = 4;
    pub const RANK0: usize = 48;
    pub const DEF_DIR: &str = "matmul/dps48";
    pub const DEF_OUT: &str = "matmul/found48p";
    pub const P: u64 = 0xFFFF_FFFF_0000_0001;
    #[inline(always)]
    pub fn fmul(a: u64, b: u64) -> u64 {
        ((a as u128 * b as u128) % (P as u128)) as u64
    }
    include!("../flip23p_engine.rs");
}

mod babybear {
    pub const DIM: usize = 4;
    pub const RANK0: usize = 48;
    pub const DEF_DIR: &str = "matmul/dps48";
    pub const DEF_OUT: &str = "matmul/found48p";
    pub const P: u64 = 2_013_265_921; // 2^31 - 2^27 + 1
    #[inline(always)]
    pub fn fmul(a: u64, b: u64) -> u64 {
        (a * b) % P // operands < 2^31: product fits u64
    }
    include!("../flip23p_engine.rs");
}

mod m31 {
    pub const DIM: usize = 4;
    pub const RANK0: usize = 48;
    pub const DEF_DIR: &str = "matmul/dps48";
    pub const DEF_OUT: &str = "matmul/found48p";
    pub const P: u64 = 2_147_483_647; // 2^31 - 1
    #[inline(always)]
    pub fn fmul(a: u64, b: u64) -> u64 {
        (a * b) % P
    }
    include!("../flip23p_engine.rs");
}

mod f2 {
    pub const DIM: usize = 4;
    pub const RANK0: usize = 49; // Strassen (x) Strassen seed (mm49)
    pub const DEF_DIR: &str = "matmul/mm49";
    pub const DEF_OUT: &str = "matmul/found48p";
    pub const P: u64 = 2; // the Kauers-Moosbauer flip-graph field
    #[inline(always)]
    pub fn fmul(a: u64, b: u64) -> u64 {
        a & b
    }
    include!("../flip23p_engine.rs");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let prime = args
        .iter()
        .position(|a| a == "--prime")
        .and_then(|i| args.get(i + 1).cloned())
        .unwrap_or_else(|| "goldilocks".into());
    match prime.as_str() {
        "goldilocks" => goldilocks::run(args),
        "babybear" => babybear::run(args),
        "m31" => m31::run(args),
        "f2" => f2::run(args),
        other => {
            eprintln!("unknown --prime {other}; use goldilocks | babybear | m31 | f2");
            std::process::exit(2);
        }
    }
}
