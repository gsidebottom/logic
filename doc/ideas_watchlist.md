# Ideas that become promising if satsuma fails their instances

Started 2026-10-04 during the SC2022 anniversary duo run (satsuma vs
hydra_circuit_satsuma, `tools/gbd/duo.py`). Each idea is a new hydra stage or
an extension of one, aimed at instances the 2022 field could not solve.
An idea only pays where satsuma also fails, because satsuma already cracks
much of what beat 2022 (php-025-024 in 0.36 s, x2_128 in 0.43 s, both
unsolved by all 28 solvers in 2022). So each idea has a watchlist of
instances, and the duo run decides it as it goes:

```bash
tools/gbd/watchlists.py
```

prints, per idea, how many of its instances satsuma has reached, solved and
failed, each failure with the 2022 field's record. The lists are in
`tools/gbd/watchlists_anni_2022.json`, built from the stage scan
(`doc/data/anni_2022_stage_scan.md`) and the SC2022 detailed results.

## 1. Cook prover recognisers for more pigeonhole encodings (113 instances, 56 unsolved in 2022)

The Cook prover decides pigeonhole, RoundRobin, embedded pigeonhole,
clique-coloring and mutilated chessboard in milliseconds with a VeriPB
certificate, but does not recognise three encodings in its own families:
relativized pigeonhole (`rphp*`, `a_/e_/ae_rphp*`), two pigeons per hole
(`tph*`), and the anniversary set's clique-coloring variants (`clqcolor*`,
`fclqcolor*`; the 2026 `clqcl` encoding is recognised). All are cardinality
contradictions with polynomial cutting-planes refutations, so the
certificate machinery carries over. Risk: satsuma's symmetry breaking is
strong on pigeonhole (it solved both rphp/tph-family instances reached so
far). Promising if it fails several of the 56.

## 2. An algebraic multiplier-miter stage (23 instances, all unsolved in 2022)

Equivalence miters of two multiplier architectures with explicit partial
products (`eq*sp*bp*`, `ak*booth*`, `custmul*`, `lec_mult*`): detectable as
circuits (gate extraction defines nearly every variable), hard for CDCL,
untouched by the circuit stage (no hidden products to recover) and by
ABC's rewriting and fraiging. The known method is algebraic: show both
circuits compute the same polynomial (Kaufmann and Biere's AMulet), with
algebraic certificates (Practical Algebraic Calculus), which would need
translating to a competition checker format. A sizeable build. First data
point: satsuma times out on eqspwtrc16bparrc16 (2022: 0/28).

## 3. A bounded local-search stage (35 satisfiable instances)

Satisfiable instances a walk-heavy 2022 solver (kissat-els, LSTech_Maple,
the HyWalk solvers) solved at least ten times faster than the rest, or
nearly alone: sgen3/sgen4, vmpc, Schur, rbsat and others. Walking heavily
everywhere loses (kissat-els-v1 finished 34th of 52 in 2022, PAR-2 145
points worse than its base), so the stage would be capped, on small
formulas only, and pays about 1.9 PAR-2 points per rescued instance against
the cap's cost on every instance (`doc/data/local_search_in_sat_competitions.md`).
Our CaDiCaL exposes the walker (`walkeffort`, `walkmaxeff`,
`walkredundant`); the satsuma image's kissat is built without options. First
data point: satsuma times out on sgen4-sat-280-8 (2022: kissat-els-v1 168 s).

## 4. Near-complete parity systems (21 instances, all unsolved in 2022)

`*.cnf.mis-N.debugged` variants of Tseitin, Urquhart and xor-chain formulas:
one clause removed, so one XOR's encoding is incomplete and the XOR stage
hands the formula on. Gaussian elimination over the complete XORs plus the
incomplete one as plain clauses, or case-splitting on its missing row, may
still decide them cheaply. Promising if satsuma fails them.

## 5. Equivalence chains (10 instances, all unsolved in 2022)

`equilarge_l*` and `equilarge_m*`: chains of equivalences the XOR stage
does not decide in their present encoding. Needs a look at the encoding
first. First data point: satsuma times out on equilarge_l5.

## Not on the list

The circuit stage applies to nothing in this set (its encoding entered the
competitions in 2025), and the cryptographic and hidden-weighted-bit
circuits are hard by design, with no known circuit method.
