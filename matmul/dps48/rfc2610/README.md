# Sedoglavic's RFC 2610 (received 2026-10-30): checks and experiments

The note, its `4x4x4_48_203_{L,R,P}` files and `slp2matsprod.py` are his and are not committed here.
Scripts take the directory holding those files and PLinOpt's `data/` as arguments; `run*.sh` hold
this session's scratchpad paths.  `results.txt`, `run.out` and `run_resc.out` are the raw output.

| point | L | R | P | total | canonical L/R rows | amp |
|---|---|---|---|---|---|---|
| Joshua's 204 | 57 | 57 | 90 | 204 | 10 / 10 | 10.44 |
| his 203 (Joshua's L, R; our P) | 57 | 57 | 89 | 203 | 10 / 10 | 10.44 |
| our 201 | 55 | 57 | 89 | 201 | 6 / 4 | 9.53 |
| DPS accurate_262 (the library's) | | | | 262 | 0 / 8 | 2.83 |

L and R each take 55 additions + 2 halvings at the 203 point.

- **Program search** (`run.sh`, lns48, 12 seeds x 180 s): L and R 57 in 48 of 48 runs, naive or seeded
  from his programs.
- **Product rescalings** (`rescale.py`, `run_resc.sh`; all six Brent-checked exactly): the 16 products
  with halves scaled by 2 give 226 (A, B: L x2 or R x2, P /2) and 238 (C: both, P /4); product 43
  alone gives 204 (D, E, F).  Control: P^T 57, so P 89.  Halves in L and R are shared signals: o43 is
  reused by four later lines, so scaling that output keeps the halving.  Heuristic search over 2 of
  the 65,536 subsets of those products, not a lower bound.
- **Map to our point** (`derive.py`): all 48 products match with scalars of exactly +-1 in L, R and P;
  U and W signed permutations, V not, W equal to his.  rho as printed does not carry the 203 files to
  the 201 files: 0 of 48 by Lemma 2.1 either way, at most 1 of 48 over all forms (`rho.py`, `rho2.py`).
