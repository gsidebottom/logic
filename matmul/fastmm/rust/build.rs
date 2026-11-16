// Links Accelerate.  With the feature gpu, also the GPU's leaf: ../gpu_leaf.m (Objective-C, the C
// library's) compiled here, and the Foundation, Metal and MetalPerformanceShaders frameworks.  With
// the feature cbench (the benchmarks that compare against the C library only), also the C library
// (../build/libfmm.a, or ../build/libfmm_gpu.a with gpu, which carries gpu_leaf.o itself) and its
// D48 left-factor kernel with its GCD pass driver (csrc/ckernels.c over ../build/kernels.h): run
// `make build/libfmm.a` (and `make build/libfmm_gpu.a`) in matmul/fastmm first.
use std::process::Command;

fn main() {
    println!("cargo:rustc-link-lib=framework=Accelerate");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_CBENCH");
    println!("cargo:rerun-if-env-changed=CARGO_FEATURE_GPU");
    let gpu = std::env::var_os("CARGO_FEATURE_GPU").is_some();
    let cbench = std::env::var_os("CARGO_FEATURE_CBENCH").is_some();
    let out = std::env::var("OUT_DIR").unwrap();
    if gpu {
        for fw in ["Foundation", "Metal", "MetalPerformanceShaders"] {
            println!("cargo:rustc-link-lib=framework={fw}");
        }
        println!("cargo:rerun-if-changed=../gpu_leaf.m");
        println!("cargo:rerun-if-changed=../gpu_leaf.h");
        if !cbench {
            let obj = format!("{out}/gpu_leaf.o");
            let ok = Command::new("clang")
                .args(["-O2", "-fobjc-arc", "-Wall", "-c", "../gpu_leaf.m", "-o", &obj])
                .status()
                .expect("clang")
                .success();
            assert!(ok, "compiling ../gpu_leaf.m");
            let lib = format!("{out}/libfmmgpu.a");
            let _ = std::fs::remove_file(&lib);
            assert!(Command::new("ar").args(["rcs", &lib, &obj]).status().expect("ar").success());
            println!("cargo:rustc-link-search=native={out}");
            println!("cargo:rustc-link-lib=static=fmmgpu");
        }
    }
    if !cbench {
        return;
    }
    let obj = format!("{out}/ckernels.o");
    let ok = Command::new("clang")
        .args(["-O3", "-mcpu=apple-m4", "-ffp-contract=off", "-Wno-unused-function", "-I../build", "-c", "csrc/ckernels.c", "-o", &obj])
        .status()
        .expect("clang")
        .success();
    assert!(ok, "compiling csrc/ckernels.c (run make in matmul/fastmm first)");
    let lib = format!("{out}/libckernels.a");
    let _ = std::fs::remove_file(&lib);
    assert!(Command::new("ar").args(["rcs", &lib, &obj]).status().expect("ar").success());
    // the C library under another name than this crate's (its GPU build with gpu)
    let c = if gpu { "../build/libfmm_gpu.a" } else { "../build/libfmm.a" };
    std::fs::copy(c, format!("{out}/libfmmc.a")).unwrap_or_else(|e| panic!("{c} (make {}): {e}", &c[3..]));
    println!("cargo:rustc-link-search=native={out}");
    println!("cargo:rustc-link-lib=static=ckernels");
    println!("cargo:rustc-link-lib=static=fmmc");
    println!("cargo:rerun-if-changed=csrc/ckernels.c");
    println!("cargo:rerun-if-changed=../build/kernels.h");
    println!("cargo:rerun-if-changed={c}");
}
