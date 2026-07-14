//! flip23p — the 3x3 flip engine over PRIME FIELDS, for the zkML
//! program (see doc/matmul_zkml_paper.md).  One binary, three
//! monomorphized fields via include!-instantiation (zero-cost:
//! every field constant folds at compile time):
//!
//!   --prime goldilocks   p = 2^64 - 2^32 + 1   (Plonky2/STARK; default)
//!   --prime babybear     p = 2^31 - 2^27 + 1   (RISC Zero; ~4x faster)
//!   --prime m31          p = 2^31 - 1          (Circle STARKs)
//!
//! All modes live in src/flip23p_engine.rs: storm (default),
//! --census, --native, --lams, and --pursue7 (mix-and-quench descent
//! with closing moves — see the engine header).

mod goldilocks {
    pub const DIM: usize = 3;
    pub const RANK0: usize = 23;
    pub const DEF_DIR: &str = "matmul/mm23";
    pub const DEF_OUT: &str = "matmul/found23p";
    pub const P: u64 = 0xFFFF_FFFF_0000_0001;
    #[inline(always)]
    pub fn fmul(a: u64, b: u64) -> u64 {
        ((a as u128 * b as u128) % (P as u128)) as u64
    }
    include!("../flip23p_engine.rs");
}

mod babybear {
    pub const DIM: usize = 3;
    pub const RANK0: usize = 23;
    pub const DEF_DIR: &str = "matmul/mm23";
    pub const DEF_OUT: &str = "matmul/found23p";
    pub const P: u64 = 2_013_265_921; // 2^31 - 2^27 + 1
    #[inline(always)]
    pub fn fmul(a: u64, b: u64) -> u64 {
        (a * b) % P // operands < 2^31: product fits u64
    }
    include!("../flip23p_engine.rs");
}

mod m31 {
    pub const DIM: usize = 3;
    pub const RANK0: usize = 23;
    pub const DEF_DIR: &str = "matmul/mm23";
    pub const DEF_OUT: &str = "matmul/found23p";
    pub const P: u64 = 2_147_483_647; // 2^31 - 1
    #[inline(always)]
    pub fn fmul(a: u64, b: u64) -> u64 {
        (a * b) % P
    }
    include!("../flip23p_engine.rs");
}

mod f2 {
    pub const DIM: usize = 3;
    pub const RANK0: usize = 23;
    pub const DEF_DIR: &str = "matmul/mm23";
    pub const DEF_OUT: &str = "matmul/found23p";
    pub const P: u64 = 2; // mod-2 flip graph (22-hunt over F_2)
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
