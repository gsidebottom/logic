# CaDiCaL 3.0.1, vendored

Upstream: <https://github.com/arminbiere/cadical>, MIT licensed (see
`LICENSE`), version per `VERSION`.  Only `src/` is kept; the upstream
`configure`/`makefile` build, the fuzzer (`mobical.cpp`), the standalone
main (`cadical.cpp`) and the C/IPASIR wrappers (`ccadical.cpp`,
`ipasir.cpp`) are not used — `/build.rs` compiles the library sources
directly with `cc`, together with `src/cadical3_shim.cpp`.

Why vendored (2026-09-17): the `cadical` crate is frozen at 0.1.16, which
bundles CaDiCaL **1.9.5**, while the certified paths shell out to whatever
`cadical` is on PATH (3.0.0 here).  Every "vs CaDiCaL" measurement taken
through `-b cadical` was therefore against 1.9.5, which on
`toughsat_factoring_895s` takes 170 s where 3.0.0 takes 19 s — a
systematic error of unknown size in `doc/box_candidates_satcomp.md`.
Vendoring puts one CaDiCaL in the binary, the same one the UI's
learned-clause panel and the benchmarks see.

`sat --backend cadical` prints the signature (`c cadical-3.0.1`) so a run's
solver is on the record.  The *certified* paths (`--backend pb-cadical`,
hydra, `tools/*certify*`) still shell out to the `cadical` on `PATH`,
because writing an LRAT/DRAT proof file wants the standalone binary and
its `--lrat` flag; the shim binds no tracer.  So two CaDiCaLs remain, but
they now differ by a patch level (3.0.0 on `PATH` here, 3.0.1 vendored)
instead of by four years.

The source is byte-identical to the copy in the `mrs-cadical-sys` 0.2.3
crate, which is where it was taken from (no network needed); that crate is
not a dependency — its shim exposes no learner callback, which the web UI
needs.
