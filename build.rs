//! Builds the vendored CaDiCaL 3.0.1 (`vendor/cadical-3.0.1`) and the
//! `extern "C"` shim that [`logic::cadical::solver`] calls into.
//!
//! This mirrors what upstream's own `configure && make` does for a release
//! build, minus the pieces a library has no use for:
//!
//! * `cadical.cpp` and `mobical.cpp` each define `main` (the standalone
//!   solver and the fuzzer); `ccadical.cpp` and `ipasir.cpp` are C and
//!   IPASIR façades we do not use.
//! * `NBUILD` tells CaDiCaL not to look for the `build.hpp` that
//!   `configure` would have generated — the two values it wants from it,
//!   `VERSION` and the compiler flags, are passed here instead.
//! * `NDEBUG` is set unconditionally.  CaDiCaL asserts heavily, and this
//!   crate uses it as a *reference solver*: a debug-profile build that
//!   measured 3× slow because `cargo test` turned its assertions on would
//!   be worse than useless.  For the same reason the optimization level is
//!   pinned at 3 rather than inherited from the cargo profile.
//!
//! `kitten.c` is C, so it gets its own compile.

use std::path::PathBuf;

/// `closefrom(2)` exists on some platforms and not others, and CaDiCaL
/// wants to know which; it is only ever used to close file descriptors
/// before forking a child.
fn has_closefrom() -> bool {
    let Some(out) = std::env::var_os("OUT_DIR") else { return false };
    let probe = PathBuf::from(out).join("closefrom_probe.cpp");
    if std::fs::write(&probe, "#include <unistd.h>\nint main(){::closefrom(3);return 0;}\n").is_err() {
        return false;
    }
    cc::Build::new().cpp(true).warnings(false).file(&probe)
        // A failing probe is the expected outcome on macOS; neither its
        // link flags nor its compiler errors are news to cargo.
        .cargo_metadata(false).cargo_warnings(false)
        .try_compile("closefrom_probe").is_ok()
}

fn main() {
    let manifest = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").expect("CARGO_MANIFEST_DIR"));
    let src = manifest.join("vendor/cadical-3.0.1/src");
    let shim = manifest.join("src/cadical/shim.cpp");

    let mut sources: Vec<PathBuf> = std::fs::read_dir(&src)
        .expect("vendored CaDiCaL source directory")
        .map(|e| e.expect("CaDiCaL source entry").path())
        .filter(|p| p.extension().is_some_and(|e| e == "cpp"))
        .filter(|p| {
            let name = p.file_name().and_then(|n| n.to_str()).unwrap_or("");
            !matches!(name, "cadical.cpp" | "mobical.cpp" | "ccadical.cpp" | "ipasir.cpp")
        })
        .collect();
    assert!(sources.len() > 80, "expected the whole CaDiCaL library, found {} sources", sources.len());
    sources.push(shim.clone());
    sources.sort();

    let mut build = cc::Build::new();
    build
        .cpp(true)
        .std("c++17")
        .warnings(false)
        .opt_level(3)
        .define("NBUILD", None)     // no generated build.hpp
        .define("NUNLOCKED", None)  // plain stdio, no *_unlocked
        .define("QUIET", None)      // no verbose/profiling machinery
        .define("NDEBUG", None)
        .define("VERSION", "\"3.0.1\"")
        .include(&src);
    if !has_closefrom() { build.define("NCLOSEFROM", None); }
    for s in &sources { build.file(s); }
    build.compile("cadical3");

    cc::Build::new()
        .warnings(false)
        .opt_level(3)
        .define("NDEBUG", None)
        .include(&src)
        .file(src.join("kitten.c"))
        .compile("cadical3_kitten");

    println!("cargo:rerun-if-changed={}", shim.display());
    println!("cargo:rerun-if-changed={}", src.display());
}
