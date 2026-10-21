# Drivers around Patel's circuit LNS (rank-48 campaign, 2026-10-21)

**Engines.**  `../../../src/bin/lns48.rs` (`cargo build --release --bin lns48`)
is our Rust reimplementation of the value-set LNS with PLinOpt's objective:
~80 iterations/s per thread, 20x the z3-free Python; it reads PLinOpt or
Patel-syntax seed programs (`--slp`) or seeds itself from the matrix
(`--sms` alone, a naive chain program), runs several seeds in threads and
re-verifies every program it writes.  The drivers below call it by default
(`LNS_ENGINE=rust`, `LNS48_BIN`); `LNS_NAIVE=1` skips the PLinOpt seed
pass; `LNS_ENGINE=python` uses `patel_phase.py` on his code instead.
`restarts.sh PREFIX OUT [SEEDS] [WALL] [SEED0]` is the naive-seed restart
campaign (L, R, P^T, assembly, SLPchecker + exact check).

R. Patel's search code for the 202-operation rational `<4x4x4:48>` circuits
(https://github.com/rp440/matmul-4x4-48-202, directory `search/`, CC0;
Python >= 3.10 and `z3-solver`) is a value-set large-neighbourhood search:
a program is its set of signal vectors, each step proposes a few new
vectors, reverse-deletes while the set stays closed under one-gate
productions, and accepts equal-cost and best+1 moves.  These scripts drive
it on our points and re-verify everything with our own tools; none of his
code is copied here.  Set `PATEL_SEARCH` to the clone's `search/` directory
and `PLINOPT_BIN` to a directory with PLinOpt's `SLPchecker`, `optimizer`,
`transpozer` and `matrix-transpose`.

- `patel_phase.py` -- run his `Search` class on ONE linear map given as a
  program (no triple admission), checking after every accepted move that
  the map is unchanged.  Used for P through its transpose: his direct
  search on the 48-input P map does not move (sparse68: 101 -> 101), while
  P^T is a 48x16 map like L and R; the result is transposed back with
  PLinOpt's `transpozer` (+32 additions, transposition principle).
- `collect.py` -- gather the best programs of his `rebuild3.py` workers and
  of the P^T runs, translate his syntax (`a*(1/2)`, which SLPchecker
  rejects) with `../slp48check.py`, verify each side with SLPchecker
  against our matrices, assemble the cheapest triple and check it exactly.
- `orbitclimb48.py` -- true-cost hill climb over single orbit moves of a
  point (GL shears with c in +-1, +-1/2, +-2 and dyadic diagonal scalings
  on X, Y, Z; per-product (a, b, 1/ab) rescalings): neighbours are
  proxy-filtered (orbit48 floor + lam * non-units), each kept one is seeded
  by PLinOpt's optimizer and evaluated with his LNS at a fixed budget per
  side (L, R, P^T); the incumbent is re-evaluated at the same budget.  Runs
  under the system python3 (numpy); the LNS subprocesses use Homebrew's.
- `deepen.py` -- several seeds x a long budget on one point's three sides
  (L, R from their best programs, P from its best P^T program; his
  annealing temperature and tabu size as options), then SLPchecker counts,
  cheapest triple, exact check.
- `neighbours48.py` -- write a point's proxy-filtered single-move (or
  depth-2) orbit neighbourhood as an orbit48-format pool for `sweep.py`.
- `assemble.py` -- cheapest verified triple of a sweep/climb candidate from
  its stage directories, with the point's matrices, checked exactly.
- `sweep.py` -- successive-halving sweep (60 s all / 300 s top 20 / 900 s x
  2 seeds top 6) over the orbit48 pool points, L and R seeded by PLinOpt's
  optimizer, P through P^T.

Counts are PLinOpt's (additions + scalings; copies and negations free);
his model also charges negations, so his numbers are upper bounds on ours.
`patel_phase.py --plinopt-model` (the default in the drivers) replaces his
z3 sign planner -- 72% of the step time in a profile, and it only
minimizes paid negations -- by his greedy plan and prices a value set by
its number of produced values: 3.3x more iterations per second (233 vs 70
in 60 s on sparse68's L, same verified result), and moves that save an
operation at the price of a negation become descents instead of plateaus.
Result on `../cand48/sparse68`: 235 -> 205 = 56 + 58 + 91 (record 202).
