# CaDiCal

Q: what is the difference between [cadical](https://docs.rs/cadical/latest/cadical/struct.Solver.html) 
and [cadical_sys](https://docs.rs/cadical-sys/latest/cadical_sys/index.html) rust crates?

A:

The cadical crate is a standalone package that includes the C++ source code of the CaDiCaL SAT solver, compiling and statically 
linking it directly into your binary during the build process.  In contrast, cadical-sys provides low-level Rust bindings 
to an external CaDiCaL library, requiring the C++ code to be present and linked separately on the system.

Key differences include:

- Deployment: cadical bundles the C++ implementation, ensuring the solver is available on any supported platform (Linux, macOS, Windows, etc.) without external dependencies, whereas cadical-sys expects the user to provide the C++ library via system packages or manual installation.

- Interface: cadical offers a safe Rust interface that wraps the C++ functionality, while cadical-sys exposes raw, unsafe bindings (via the cxx crate) to the C++ API, giving direct access to the solver's internal mechanisms.
- Use Case: cadical is ideal for projects requiring a zero-configuration, self-contained solution, while cadical-sys is preferred when integrating with an existing C++ environment or when needing to share bindings across multiple safe wrappers.

## Streamlined Rust API


## Full Rust API
