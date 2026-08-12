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

Per-instance overhead: one `docker run` per phase (~0.3-0.9 s each on
this machine); UNSAT verification is a second, separately-budgeted run.

## Bounds and controls (sat flags, drivable via run_benchmark --sat-arg)

- Solve: bounded by `timeout` inside the container at the remaining
  budget minus 2 s, so the container always self-terminates and can
  never outlive sat's backstop watchdog (no orphaned containers).
- `--satsuma-verify-secs N` (default: same as --timeout, matching
  run_benchmark's --proof-timeout convention for the hydra chain;
  0 = unlimited): dsr-trim budget. Runs AFTER the verdict + timing line land (verification never
  eats solve budget or inflates recorded solve time). On timeout the
  UNSAT stays sound but is recorded UNCERTIFIED ("dsr-trim timeout").
- `--satsuma-mem-gb N` (default 0 = uncapped): per-container hard cap
  (docker --memory/--memory-swap). An instance that exceeds it fails
  alone (recorded TIMEOUT/unknown) instead of destabilizing neighbors.
- Size guard (built in): instances with >= 1M vars or >= 25M clauses
  skip satsuma (its literal graph is several GB there — the winning
  submission's own guard, shipped commented-out on 128 GB nodes) and
  run kissat directly; still solved, UNSAT still dsr-trim-checkable.

## Docker VM memory (IMPORTANT)

Docker Desktop's VM allocation bounds ALL containers TOGETHER. At
-j 10 with the default ~8 GiB, big instances are OOM-killed
in-container and surface as fast TIMEOUTs. Raise it to ~48 GB in
Docker Desktop -> Settings -> Resources -> Memory before a full
benchmark run; run_benchmark warns at startup when the allocation is
under 4 GiB x parallel workers.
