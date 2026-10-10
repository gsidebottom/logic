# Unique wins over satsuma: 2026 measured, 2022 anniversary so far, 2025 expected

2026-10-10. A unique win is an instance hydra_circuit_satsuma solves within
5,000 s and satsuma does not. Since hydra_circuit_satsuma hands every other
instance to the same satsuma, its unique wins come only from instances a
stage decides, or the circuit stage rewrites, and satsuma fails.

| set | instances | unique wins | density | source |
|---|---|---|---|---|
| SC2026 main track | 391 | 4 | 1.0% | October runs, `doc/competition-benchmark_main_track_2026_official_5000_{hydra_circuit_satsuma_2,satsuma_2}.json` |
| SC2022 anniversary, first 4,369 | 4,369 | 6 | 0.14% | duo run, 82% done; 8 expected of 5,355 (0.15%) |
| SC2025 main track | 400 | 4 to 5 expected | about 1.1% | this scan |

Nothing went the other way: satsuma has no instance the other arm misses.

2026: gm16spwtrc, gm20spctrc, gm16spwtcl (circuit stage, CaDiCaL on the
rewritten formula) and mchess_20 (Cook prover). 2022 anniversary so far:
pmg-14, eulcbip-8, pmg-13, eulcbip-9 (XOR stage, GN21 proofs),
mod2-rand3bip-sat-300-3 (XOR stage, model) and mchess_20 (Cook).

## SC2025: how the expectation was built

All 400 instances are on disk (`sat_benchmarks/main_track_2025_official.jsonl`,
from GBD `track=main_2025`). 118 are also in the 2026 main track and 100 in
the anniversary set, so 195 already have a measured satsuma / hydra pair
(118 from the October 2026 run, 77 from the duo run so far). For the rest,
`tools/gbd/stage_scan.py` (stages only, no engine) and `tools/gbd/sym_probe.py`
(satsuma's symmetry step alone) ran in `sat_benchmarks/runs/main_2025_scan/`,
read with the anniversary calibration: an instance the symmetry step alone
refutes is a satsuma solve in seconds (35 of 35 there).

Stage scan: Cook 24, XOR 5, factoring 5, circuit stage would fire 6
(gm16spctrc, gm24sparrc, gm28sparrc, gm16sparrc, pj2008_k80, pj2009_k80);
fall-through 360. The 40 instances:

| instance | stage | satsuma | expectation |
|---|---|---|---|
| mchess_20 | Cook | measured 2026: timeout | unique, measured |
| tseitin_grid_n400_m400, 319,200 vars | XOR, 556 s | symmetry step finds 45 generators, fixes 36 variables | unique, near certain |
| tseitin_grid_n250_m250, 124,500 vars | XOR, 64 s | 47 generators, 31 variables fixed | unique, near certain |
| tseitin_d3_n100000, 150,000 vars | XOR, 94 s | 30 generators, 22 variables fixed | unique, near certain |
| gm16sparrc | circuit | satsuma solved the 16-bit ct and the 24- and 28-bit ar siblings in 2026 | low |
| pj2008_k80, pj2009_k80 (SAT, hardware model checking) | circuit | 2025 solvers solved them | low |
| 11 RoundRobin, 8 clique-coloring, harder-fphp-016-015 | Cook | 14 measured solves; the other 6 refuted by the symmetry step alone, except cliquecoloring_n14_k7_c6 (273 vars, 118 fixed) | none |
| 3 purdom, Carry_Bits_Fast_19, Wallace_Bits_Fast_8 (SAT) | factoring | no symmetry, but every factoring-decided instance so far was a satsuma solve (28 of 28 solvers in 2022, solved in 2025) | none to low |
| tseitin_n188_d3, tseitin_grid_n12_m12 | XOR | refuted by the symmetry step alone | none |

The three large Tseitin formulas are the new ingredient. On the
anniversary grids (2,100 to 2,800 variables) satsuma's symmetry step finds
1,200 to 2,200 generators, fixes about 950 variables and kissat finishes in
12 s. On the 2025 grids it stops after a few dozen generators, so kissat
meets a Tseitin formula with over 100,000 variables, which resolution cannot
refute. GBD records all three as never solved by anyone, including the 2025
satsuma entry. The XOR stage decides them by Gaussian elimination with a
GN21 parity proof.

Expected count: 1 measured + 3 near certain + about 0.5 across the low
rows = 4 to 5, a density of about 1.1%, the same as 2026. The anniversary
set's lower density (0.15%) has a reason: its parity and pigeonhole
families are small enough that satsuma's symmetry breaking refutes 207 of
the 264 stage-decided instances outright. The newer sets carry the
instances where that breaks down: larger Tseitin grids, mchess_20, and the
gm multiplier miters, whose family entered the competitions in 2025.

To settle the near-certain rows, run satsuma alone on tseitin_grid_n250_m250
(up to 83 minutes); not done while the anniversary run holds the cores.
