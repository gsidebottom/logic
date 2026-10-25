//! fmm: fast matrix multiplication on Apple silicon, in Rust.
//!
//! Feasibility stage: the fused passes of the fast schemes are safe Rust (`kernels`, generated
//! by `gen_kernels.py --rust` from the schemes' programs; `pass`, their multi-threaded drivers);
//! the products run on Apple's Accelerate GEMM, reached through the crate's only unsafe code,
//! the FFI declarations in `accelerate`.
#![deny(unsafe_code)]

pub mod accelerate;
pub mod kernels;
pub mod pass;
