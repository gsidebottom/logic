# Where hydra's stages and the circuit stage apply in the 2022 anniversary set

Scan of all 5,355 instances, 2026-10-04, with `tools/gbd/stage_scan.py`:
`sat -b hydra_circuit_satsuma --stop-at-fallthrough` with the circuit
trigger's product threshold out of reach, so Cook / XOR / factoring decide
for real and the circuit stage only reports its trial factoring, to which
the trigger (>= 64 products, paired gates >= 5% of gates, >= 20 paired gates
per product, <= 10M clauses) is applied offline. No engine runs. Results
per instance: `sat_benchmarks/runs/anni_2022_duo/stage_scan.jsonl`.
Crossed with the SC2022 anniversary track's 28 sequential solvers.

| outcome | instances | share | unsolved by all 28 in 2022 | solved by at most 14 of 28 |
|---|---|---|---|---|
| decided by the XOR stage | 167 | 3.1% | 71 | 80 |
| decided by the Cook prover | 84 | 1.6% | 58 | 65 |
| decided by the factoring stage | 13 | 0.2% | 0 | 0 |
| circuit stage would fire | 0 | 0% | 0 | 0 |
| handed on, circuit declines | 4,919 | 91.9% | | |
| handed on, over the circuit clause cap | 172 | 3.2% | | |

Hydra's stages decide 264 instances (4.9%), each in milliseconds with a
certificate (XOR: 155 UNSAT with GN21 VeriPB proofs, 12 pure-XOR SAT with
the model; Cook: 84 UNSAT with VeriPB proofs; factoring: 13 SAT with the
model). Of the 1,010 instances no 2022 solver solved, they decide 129
(12.8%). The circuit stage fires on none: the GenMul multiplier encoding
it targets is a 2026 family.

By family (decided / in the set): tseitin-formulas 147/195, pigeon-hole
56/122, coloring 18/243, xor-chain 13/22, mutilated-chessboard 10/10,
long-learned-clauses 7/11, purdom-instances 7/15, prime-factoring 6/51.

Not a 2022 solve is not a unique solve here: satsuma's symmetry breaking
also cracks many of these (php-025-024 in 0.36 s, x2_128 in 0.43 s, both
unsolved by all 28 in 2022). The next section says which.

## Which stage instances satsuma decides anyway (2026-10-05)

In reuse mode a unique win for hydra_circuit_satsuma needs an instance one
of its stages decides and satsuma fails. Every other instance takes
satsuma's result. `tools/gbd/sym_probe.py` ran satsuma's symmetry step
alone, with the competition flags and no kissat, on the 264 instances the
stages decide. Per instance: `sat_benchmarks/runs/anni_2022_duo/sym_probe.jsonl`.

| satsuma's symmetry step alone | instances | unsolved by all 28 in 2022 | satsuma in the duo run, first 654 instances |
|---|---|---|---|
| derives the empty clause | 207 | 107 | 35 of 35 solved, median 0.30 s, max 13.8 s |
| fixes variables, does not refute | 30 | 20 | 2 of 2 solved, 11.5 s and 11.9 s |
| finds no symmetry | 27 | 2 | 9 of 10 solved; the failure is pmg-14 |

Structure decides which row an instance lands in, measured by reading the
complete XOR encodings in each instance's clauses:

- Tseitin, Urquhart and xor-chain instances encode their parities as plain
  XOR clauses, and every variable sits in exactly two of them. Flipping the
  variables around any cycle of the underlying graph is then a symmetry,
  and breaking those flips leaves nothing to search. On the Tseitin grids
  the step fixes 900 to 1,000 variables and kissat finishes in seconds.
- pmg-N and eulcbip-N are Tseitin formulas inside cardinality encodings:
  exactly one of three edges at each vertex in pmg, exactly two of four in
  eulcbip, with one twisted pair making the total parity odd. Each vertex's
  clauses hold a complete XOR encoding, which the XOR stage reads, and one or
  two extra clauses, which destroy the cycle flips. satsuma finds no
  symmetry on pmg-13 and pmg-14 and fixes at most one variable on the others,
  so kissat meets a Tseitin formula at full strength.
- The random parity systems, mod2-rand3bip and mod2-3g14, put every variable
  in three equations, so no flips exist. Their satisfiable members come down
  to search luck: satsuma beat 2022's best time on all five reached so far,
  280-1 in 36 s against 278 s.

Prediction for the rest of the run. Six instances no 2022 solver solved are
both stage-decided and untouched by satsuma's symmetry step: pmg-13 #1774,
pmg-12 #3673, eulcbip-8 #939, eulcbip-9 #3495, eulcbip-7 #4948 and mchess_19
#5036. pmg-14, their sibling, was the run's first unique win. Next come
mchess_20 #1674, which satsuma did not solve in our 2026 main-track runs, and
mchess_17 #1110, which it solved there in 4,379 s. mod2-rand3bip-sat-300-3
#3458, solved by 2 of 28 in 2022, is an outside chance. The 13 Tseitin grids
left will be speed wins only.

## Misses: target families the stages do not recognise

Instances in the stages' families that no 2022 solver solved and that the
stages hand on:

- relativized pigeonhole (rphp*): 18 of 33 unsolved in 2022, none decided;
- two pigeons per hole (tph*): 12 unsolved in 2022, none decided;
- clique-coloring variants (fclqcolor*, clqcolor*): 19 unsolved in 2022,
  none decided (the 2026 clqcl encoding is recognised, these are not);
- mod2 / Urquhart / xor-chain "*.cnf.mis-N.debugged" variants: one clause
  removed from a parity formula, so the XOR system is no longer complete
  and the XOR stage rightly hands it on.

About 49 instances (rphp, tph, fclqcolor/clqcolor) are candidates for
extending the Cook prover's recognisers, worth it where satsuma does not
already solve them.
