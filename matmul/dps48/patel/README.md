# Drivers around Patel's circuit LNS (rank-48 campaign, 2026-10-21)

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
- `sweep.py` -- successive-halving sweep (60 s all / 300 s top 20 / 900 s x
  2 seeds top 6) over the orbit48 pool points, L and R seeded by PLinOpt's
  optimizer, P through P^T.

Counts are PLinOpt's (additions + scalings; copies and negations free);
his model also charges negations, so his numbers are upper bounds on ours.
Result on `../cand48/sparse68`: 235 -> 205 = 56 + 58 + 91 (record 202).
