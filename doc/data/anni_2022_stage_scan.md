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
unsolved by all 28 in 2022); the duo run decides that instance by instance.

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
