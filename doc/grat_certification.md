# GRAT certification for the kissat UNSAT path

The pb-cadical / hydra portfolio runs **kissat** for the first slice of the
budget (fast SAT detection + the occasional fast UNSAT). When kissat decides
UNSAT and a proof is requested, it emits a **binary DRAT** trace, which must be
turned into a checkable certificate. We previously elaborated that DRAT to LRAT
with **drat-trim** and checked it with **cake_lpr**. We now elaborate it to a
**GRAT** certificate with **gratgen** and check it with the formally-verified
**gratchk** ([Lammich, GRAT tool chain](https://www21.in.tum.de/~lammich/grat/)).

The CaDiCaL path is unchanged (native LRAT → cake_lpr); the Cook/XOR paths are
unchanged (VeriPB pbp → veripb). Only the **kissat** path moved to GRAT.

## Why

Profiling the kissat-UNSAT certifications in the 2025/2026 main-track runs
surfaced three failure modes of the drat-trim → cake_lpr chain, none of which a
larger *time* budget fixes:

1. **Trivial-UNSAT proofs dropped.** When the formula is UNSAT by unit
   propagation alone, drat-trim prints `s VERIFIED` but writes a **0-byte
   LRAT** and exits non-zero, so the pipeline recorded "no proof emitted".
   (Most of the 8/3 kissat-UNSAT certification failures in 2025/2026.)
2. **drat-trim is slow + single-threaded.** On harder proofs it runs many
   minutes (e.g. a 248 MB DRAT took >15 min, never finishing in our 900 s cap),
   badly violating the "verification < production" goal.
3. **cake_lpr is memory-heavy.** Its formula representation needs RAM ≈ proof
   size; on a 56.7M-clause instance it needed ~44 GB just to load the formula —
   over the SAT-Competition **30 GB** limit — and OOM'd.

GRAT addresses all three: gratgen handles the trivial case, is **parallel**
(`-j`), and gratchk's checker memory is markedly lower than cake_lpr's.

## Benchmark — drat-trim+cake_lpr vs gratgen+gratchk

18 representative kissat-UNSAT instances (solve 4–27 s, 169 vars … 23.8M
clauses), same binary DRAT fed to both pipelines. Times in seconds, memory in
MB (peak RSS); `⏱` = hit the 300 s per-stage cap. M4 Pro, gratgen `-j8`.

<!-- generated from tools — see commit message -->
| instance | drat MB | drat-trim s | cake_lpr s/MB | ✓ | gratgen s/MB | gratchk s/MB | ✓ |
|---|--:|--:|--:|:-:|--:|--:|:-:|
| b20_1 | 14 | 2 | 1/537 | ✓ | 1/260 | 1/248 | ✓ |
| gm24sparrc | 0 | 0 | 1/867 | ✓ | 0/1 | 0/2 | ✓ |
| hwmcc17miters-xits-iso-6s299b685 | 4 | 9⏱ | — | ✗ | 20/11353 | 8/7130 | ✓ |
| b21 | 19 | 4 | 1/986 | ✓ | 1/321 | 1/299 | ✓ |
| SCPC-500-13 | 14 | 6 | 2/1891 | ✓ | 2/263 | 2/985 | ✓ |
| b22_1 | 25 | 4 | 1/1032 | ✓ | 1/383 | 1/305 | ✓ |
| b22 | 25 | 4 | 1/1016 | ✓ | 1/386 | 1/301 | ✓ |
| gm28sparrc | 1 | 1 | 1/1508 | ✓ | 1/201 | 1/241 | ✓ |
| SCPC-500-5 | 22 | 8 | 2/2364 | ✓ | 2/358 | 3/1326 | ✓ |
| battleship-13-13-unsat | 46 | 15 | 5/7148 | ✓ | 5/767 | 7/3012 | ✓ |
| uniqinv40prop | 65 | 8 | 3/3411 | ✓ | 3/889 | 4/2019 | ✓ |
| oddball_13_5_ttf.normalised | 104 | 35 | 11/16058 | ✓ | 9/1619 | 15/10308 | ✓ |
| velev-pipe-o-uns-1.1-6 | 89 | 37 | 2/2774 | ✓ | 6/1127 | 3/1300 | ✓ |
| SCPC-500-14 | 40 | 16 | 4/4608 | ✓ | 4/628 | 4/1657 | ✓ |
| pj2013_k9 | 161 | 45 | 4/9070 | ✓ | 10/4394 | 3/1662 | ✓ |
| linked_list_swap_contents_safety_unwind50 | 570 | 300⏱ | — | ✗ | 56/20220 | 19/10446 | ✓ |
| b17 | 58 | 16 | 3/3332 | ✓ | 4/793 | 4/1688 | ✓ |
| SCPC-500-12 | 64 | 27 | 6/7409 | ✓ | 6/1003 | 7/3015 | ✓ |

**Aggregate:**
- **Certified: GRAT 18/18 vs drat-trim+cake_lpr 16/18.** GRAT recovered the two
  the old chain lost: `hwmcc` (trivial-UNSAT empty proof) and `linked_list`
  (drat-trim timed out at 300 s; gratgen elaborated it in 56 s).
- **Elaboration 4.0× faster:** gratgen 133 s total vs drat-trim 537 s
  (median 3.0 s vs 8.7 s).
- **Checker memory lower** (the 30 GB-relevant axis): gratchk median 1.5 GB /
  max 10.4 GB vs cake_lpr 2.6 GB / max 16 GB. (E.g. `pj2013`: 1.7 GB vs 9.1 GB.)

**Trade-off — gratgen elaboration memory.** Parallelism costs RAM: gratgen
median 0.7 GB / max 20 GB vs drat-trim's frugal 0.2 GB median. All 18 stayed
under 30 GB at `-j8`, but the 56.7M-clause `hash_table` outlier hit 36 GB at
`-j8` — for a 30 GB-capped node, lower `--elab-jobs` (e.g. `-j2`) to fit.

## Wiring

- **`src/bin/sat.rs`** — the kissat elaboration block runs
  `gratgen <cnf> <drat> -b -o <out> -j <N> --no-progress-bar` (binary DRAT in,
  combined GRAT out), bounded by `--elab-time-s` / `--elab-mem-mb`, with
  `--elab-jobs N` (default 8) for threads. Verdict (`s VERIFIED`) is read from
  gratgen's **stderr**. On success it prints `proof-format=grat`.
- **`tools/gbd/run_benchmark.py`** — `verify_pb_proof` gained a `grat` branch
  (`gratchk unsat <cnf> <proof>`, `s VERIFIED UNSAT`); the checker is now keyed
  off the deciding `prover` marker (kissat → gratchk, cadical → cake_lpr,
  cook/xor → veripb), avoiding the generic format pre-announcement shadowing
  kissat's grat.
- **`setup.sh`** — Step 2.5 builds + installs gratgen + gratchk into
  `~/.cargo/bin` (skip with `--no-grat`; idempotent).

## Build notes

- **gratgen** (C++): needs Boost headers. Boost ≥ 1.90 removed the deprecated
  `<boost/progress.hpp>` it includes, so compile with
  `-DBOOST_TIMER_ENABLE_DEPRECATED`:
  `c++ -O3 -DNDEBUG -DBOOST_TIMER_ENABLE_DEPRECATED -std=c++11 -pthread -I<boost-inc> -o gratgen gratgen.cpp`
- **gratchk** (SML, Isabelle-extracted): needs **MLton**; `make` in the
  `gratchk-sml/` distribution.
- Options go **after** the positionals (`gratgen cnf drat -b -o out -j 8`);
  `-j8` (no space) is rejected — use `-j 8`.

## Trust model

Unchanged in rigor: gratgen is an **unverified** generator, gratchk is the
**formally-verified** (Isabelle/HOL) checker — exactly mirroring
drat-trim(unverified) → LRAT → cake_lpr(verified). A bad elaboration is
*rejected* by gratchk, never falsely accepted. We now run two verified
checkers (cake_lpr for the CaDiCaL path, gratchk for the kissat path); both are
SAT-Competition-grade.
