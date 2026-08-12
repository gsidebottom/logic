# satsuma-iter+kissat (SAT Competition 2026 main-track winner) as a hydra fall-through

`sat -b hydra_satsuma` = the hydra pipeline (Cook PB-prover → XOR/GE) whose
no-shape fall-through is the actual 2026 winner instead of bare CaDiCaL:

    satsuma fix f.cnf --bsr --proof-file proof.out --out-file sb.cnf   # symmetry breaking + binary-SR proof
    kissat sb.cnf proof.out                                            # appends its refutation
    dsr-trim -f f.cnf proof.out                                        # verifies the COMPOSED proof vs the ORIGINAL

so a non-GE UNSAT comes back **checker-certified** (`dsr-trim VERIFIED UNSAT`)
even when symmetry breaking fired — the capability our native Rust port
(`hydra_sym_break`) does not have yet. SAT models are projected to the
original variables. On a GE residual the certificate covers the residual
only (flagged uncertified, like hydra's XOR path).

## Build

    tools/satsuma/build.sh        # needs Docker running

Builds image `satsuma-iter-kissat` from the official competition tarball
(archived at ~/projects/sat_benchmarks/archive/anders_satcomp2026.tar.xz;
source https://satcompetition.github.io/2026/downloads/solvers/anders.tar.xz —
submission by Markus Anders et al.; components: satsuma (dejavu-based
symmetry breaking, GPL-bundled sources), kissat, dsr-trim/lsr-check).
Note: dsr-trim ships prebuilt x86-64 binaries; the Dockerfile force-rebuilds
them natively (the stale ELFs die under Rosetta on ARM hosts).

## Benchmark

    tools/gbd/run_benchmark.py --index <index.jsonl> -b hydra_satsuma -t 5000 ...

Result files carry the backend in the name (…_hydra_satsuma.{md,json}).
run_benchmark credits UNSAT certification from the solver's own
`dsr-trim VERIFIED UNSAT` marker (no --proof pass: the proof is binary SR,
which cake_lpr/veripb/gratchk do not read).

Per-instance overhead: one `docker run` (~0.3-0.9 s on this machine).
