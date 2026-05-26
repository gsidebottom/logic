# Cook 1976 PHP proof in VeriPB — walkthrough and results

## Goal achieved

**Polynomial-size, VeriPB-verified UNSAT proofs of PHP-N-M for any N > M ≥ 2.**

`tools/cook_php_proof.py N M out_dir` generates `php_N_M.cnf` +
`php_N_M.pbp`. VeriPB verifies in milliseconds even at large N.

## Measured scaling

| Problem | CNF clauses | PBP lines | VeriPB time |
|---------|-------------|-----------|-------------|
| PHP-4-3 | 22 | 120 | 10 ms |
| PHP-5-4 | 45 | 378 | 8 ms |
| PHP-6-5 | 81 | 880 | 9 ms |
| PHP-7-6 | 133 | 1,746 | 10 ms |
| PHP-8-7 | 204 | 3,120 | 15 ms |
| PHP-10-9 | 415 | 8,088 | 16 ms |
| PHP-12-11 | 738 | 17,416 | 19 ms |
| PHP-15-14 | 1,485 | 44,098 | 55 ms |
| PHP-20-19 | 3,630 | 144,408 | 119 ms |

Asymmetric cases (N > M+1) verify too: PHP-10-5 in 2,864 lines.

Proof size growth: ~O(N⁴) matching Cook's bound. Verification time
is sub-linear in proof size (VeriPB's pol verification is fast).

## Cook's construction (recap)

For PHP-n (n pigeons, n-1 holes):

- Atoms `P_{i,j}` for i ∈ [1,n], j ∈ [1,n-1].
- Pigeon clauses: `P_{i,1} ∨ ... ∨ P_{i,n-1}` for each i.
- Mutex: `¬P_{i,k} ∨ ¬P_{j,k}` for i < j, each k.

**Extension** introduces `Q_{i,j}` for i ∈ [1,n-1], j ∈ [1,n-2]:

> `Q_{i,j} ≡ P_{i,j} ∨ (P_{i,n-1} ∧ P_{n,j})`

Intuitively: "if we remove pigeon n and hole n-1, where does pigeon
i end up in the reduced map?" If `i` was already in some hole
`j ≠ n-1`, it stays; if `i` was in hole `n-1`, it moves to wherever
pigeon `n` had been.

**Four defining clauses** per `Q_{i,j}`:

```
C1: Q_{i,j} ∨ ¬P_{i,j}                              [P_{i,j} → Q_{i,j}]
C2: Q_{i,j} ∨ ¬P_{i,n-1} ∨ ¬P_{n,j}                 [(P_{i,n-1} ∧ P_{n,j}) → Q_{i,j}]
C3: ¬Q_{i,j} ∨ P_{i,j} ∨ P_{i,n-1}                  [Q_{i,j} → P_{i,j} ∨ P_{i,n-1}]
C4: ¬Q_{i,j} ∨ P_{i,j} ∨ P_{n,j}                    [Q_{i,j} → P_{i,j} ∨ P_{n,j}]
```

**Derivation**: from S_n + Q definitions, derive S_{n-1} on Q atoms
(Q-pigeon clauses + Q-mutex clauses). Then recurse n-2 times to
arrive at `S_2 = {R_1, R_2, ¬R_1 ∨ ¬R_2}`, trivially UNSAT.

## VeriPB encoding

### Introducing fresh Q variables

Each Q's 4 clauses are added via `red` rules with constant
witnesses (`Q -> 0` or `Q -> 1`). The substitution makes the new
constraint trivially true; F is unchanged because Q is fresh.
VeriPB autoproves these.

```
red 1 Q11 1 ~x1 >= 1 : Q11 -> 1 ;             # C1
red 1 Q11 1 ~x3 1 ~x10 >= 1 : Q11 -> 1 ;      # C2
red 1 ~Q11 1 x1 1 x3 >= 1 : Q11 -> 0 ;        # C3
red 1 ~Q11 1 x1 1 x10 >= 1 : Q11 -> 0 ;       # C4
```

### Deriving Q-pigeon clauses

`Q_{i,1} + ... + Q_{i,n-2} >= 1`: derived via a chain of `pol`
steps (3M-2 per Q-pigeon clause, where M = n-1 holes):

1. `E = pigeon_i + mutex(i, n, M)`  — eliminate `P_{i,n-1}`
2. `F = E + pigeon_n`               — eliminate `P_{n,n-1}`
3-M:   `G_k = prev + C1_{i,k}`      — eliminate each `P_{i,k}`
M+1..2M-1: `I_k = prev + C2_{i,k}`  — eliminate each `P_{n,k}`
2M:    `K = prev + pigeon_i`        — re-derive
2M+1..3M-1: `L_k = prev + C1_{i,k}` — final elimination

Each step is `pol C1 C2 + s` (resolution + saturate).

### Deriving Q-mutex clauses

`¬Q_{i,k} + ¬Q_{j,k} >= 1`: case split on `P_{n,k}` (7 pol per
clause):

**Case 1** (give `~Q_i + ~Q_j + P_{n,k} >= 1`):
- `R1 = C4_i + mut(i,j,k)`
- `R2 = R1 + C4_j`

**Case 2** (give `~Q_i + ~Q_j + ¬P_{n,k} >= 1`):
- `σ = C3_i + mut(i,n,k)`
- `σ' = σ + mut(i,j,M)`
- `σ'' = σ' + C3_j`
- `case2 = σ'' + mut(j,n,k)`

**Combine**: `pol case1 case2 + s` → `~Q_i + ~Q_j >= 1` (the two
`P_{n,k}` literals cancel, leaving the target).

### Closure (innermost layer)

After M-2 reductions we have PHP-(N-M+2)-2. This is in the
arity-2-pigeon-clause regime, so a single `red` with cyclic-pigeon
witness + `rup` closes it (autoproves via BCP cascade as
documented in [`pbp_emission.md`](pbp_emission.md)).

For PHP-N-1 (N pigeons in 1 hole, when N > M+1 and we end with
M=1): the closure is just `rup >= 1 ;` since N pigeon clauses
each force one specific lit, and pairwise mutex on that lit
contradicts immediately.

## Why this matters

Before this work:
- DRAT/RUP proofs of PHP-N-M (M ≥ 3) are exponential (Haken 1985).
- Our `--emit-drat` and `--emit-pbp` produced sound prefix proofs
  but couldn't close PHP-4-3 and beyond.
- The matrix-method cover certificate proved UNSAT but verifier
  was equivalent in hardness to the original problem.

Now:
- We have a parametric Cook-style PHP proof generator producing
  VeriPB-verified polynomial-size proofs at arbitrary scale.
- PHP-20-19 verified in 119 ms (vs. exponential resolution proofs).
- Same construction template (with adaptations) should crack
  RoundRobin-class cardinality problems — that's Phase 3.

## RoundRobin small case verified (n=4)

`tools/cook_rr_proof.py n d out_dir` generates RR(n teams, d days) CNF
+ VeriPB cardinality proof via:

1. Per (team, day) at-most-1 via sum of C(K,2) mutex / (K-1).
2. Per day at-most-n/2 via sum of n team's at-most-1 / 2.
3. Total at-most-d·n/2 via sum over days.
4. Pigeon-sum at-least-C(n,2).
5. Combine → contradiction (sum_x + sum_~x = const > 2·const).

| Problem | CNF clauses | PBP lines | VeriPB | Verdict |
|---------|-------------|-----------|--------|---------|
| RR n=4 d=1 | 18 | 26 | 9 ms | **VERIFIED UNSAT** |
| RR n=4 d=2 | 36 | 31 | 15 ms | **VERIFIED UNSAT** |
| RR n=6 d=2 | 150 | 35 | 9 ms | **VERIFIED UNSAT** |
| RR n=6 d=4 | 345 | 49 | 17 ms | invalid (step 1 fails) |
| RR n=16 d=13 | 31,320 | 242 | — | invalid (same wall) |

The wall: Step 1 (at-most-1 per team-day) only works when K = n−1 = 3,
because pol-sum of 3 pairwise mutex / 2 with round-up gives at-most-1.
For K ≥ 5, pol-sum of C(K,2) / (K-1) gives only at-most-⌊K/2⌋.

This is the same at-most-1-from-pairwise-mutex wall we hit in PHP.

**Fix for next session**: apply Cook's PHP machinery to each
(team, day) at-most-1 derivation. For n=16, that's 208 team-days
× O(K²) aux vars + pol steps. Polynomial but a substantial scale-up
of the proof.

## Next: adapting to RoundRobin (full size)

RoundRobin n16_d13 has structure:
- 120 "matches" (pigeons), 13 "days" (holes).
- Each match plays on some day (pigeon clauses).
- Each (team, day) slot fits at most 1 match (not pairwise per-day
  mutex; per-team-per-day).
- UNSAT by counting: 120 matches × 1 day each > 13 days × 8 slots = 104.

The Cook reduction needs adaptation: instead of "pigeons share a
hole are mutually excluded (pairwise)", we have "matches sharing
a team on a day are mutually excluded". The Q-vars and the
reduction's mutex-derivation chain will be different.

See Phase 3 tasks in `cook_extension_project.md`.

## Implementation references

- `tools/cook_php_proof.py` — the generator.
  - `Layer` class abstracts each reduction level.
  - `emit_layer_reduction` does one reduction step.
  - `emit_closure` handles the innermost step (M=1 or M=2).
- `doc/cook_extension_project.md` — multi-session project plan.
- `doc/veripb_extension_notes.md` — extension-variable mechanics
  in VeriPB.
- `doc/pbp_emission.md` — earlier `--emit-pbp` work (RUP+pol only;
  bounded by resolution lower limits).
