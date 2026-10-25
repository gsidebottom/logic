// Links Accelerate.  With the feature cbench (the benchmarks that compare against the C library
// only), also the C library (../build/libfmm.a) and its D48 left-factor kernel with its GCD pass
// driver (csrc/ckernels.c over ../build/kernels.h): run `make build/libfmm.a` in matmul/fastmm
// first.
use std::process::Command;

fn main() {
    println!("cargo:rustc-link-lib=framework=Accelerate");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_CBENCH");
    if std::env::var_os("CARGO_FEATURE_CBENCH").is_none() {
        return;
    }
    let out = std::env::var("OUT_DIR").unwrap();
    let obj = format!("{out}/ckernels.o");
    let ok = Command::new("clang")
        .args(["-O3", "-mcpu=apple-m4", "-Wno-unused-function", "-I../build", "-c", "csrc/ckernels.c", "-o", &obj])
        .status()
        .expect("clang")
        .success();
    assert!(ok, "compiling csrc/ckernels.c (run make in matmul/fastmm first)");
    let lib = format!("{out}/libckernels.a");
    assert!(Command::new("ar").args(["rcs", &lib, &obj]).status().expect("ar").success());
    // the C library under another name than this crate's
    std::fs::copy("../build/libfmm.a", format!("{out}/libfmmc.a")).expect("../build/libfmm.a (make build/libfmm.a)");
    println!("cargo:rustc-link-search=native={out}");
    println!("cargo:rustc-link-lib=static=ckernels");
    println!("cargo:rustc-link-lib=static=fmmc");
    println!("cargo:rerun-if-changed=csrc/ckernels.c");
    println!("cargo:rerun-if-changed=../build/kernels.h");
    println!("cargo:rerun-if-changed=../build/libfmm.a");
}
