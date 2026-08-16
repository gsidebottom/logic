# Asymmetric (free-weight-side) op-minimization — 3x3 rank-23 results

Objective: zkML inference has constant W, so adds on the scheme side
holding W are precomputed (free). Online cost = b-side (live input) +
c-side (output recombination), minimized over the 6 tensor orientations.

## Result: online 40 is optimal for the DB stratum (certified)

- Search (asymscore, exact signed sides + transposition-principle exact
  C, 12 sign models): best online = 40 = b13 + c27, achieved by ~7k
  schemes (e.g. found55/hunt54/reps/i46w213c23ci-016-v2-s26-90_16_11).
- Certified floor (asymfloor, exact GF(2) side floors + transposition,
  min over orientations), all 167,512 classes:
    floor 40: 7,784 classes   <- minimum; NO class floors at 39
    floor 41: 121,430 | 42: 15,552 | 43: 21,170 | 44: 61 | 45: 181
- The 55-add symmetric record (i19 class, a13+b14+c28) floors at 41
  online: the record class provably cannot reach 40; the online-40
  winners have symmetric totals 56-57 (rejected by the symmetric hunt,
  optimal under the asymmetric objective).

Scope: all {-1,0,1}-signed realizations of the enumerated mod-2
classes (same stratum scope as the 55-minimality result).

## Final census (complete over every class that could reach 40)

- 145,951 candidates scored; the remaining ~21.6k were skipped by
  design — their certified floors are >= 41, so they provably cannot
  beat 40 (the floor sweep covers all 167,512 classes).
- Of the 7,784 floor-40 classes: 7,781 achieve online 40 (floor tight,
  99.96%); exactly one scheme (i46w205c23ci-017-v4-s26-54_120_44,
  stored in 3 directories) floors at 40 but achieves only 41 — a
  genuine sign obstruction: no {-1,0,1} realization of that class
  meets its GF(2) floor.

Headline: fixed-weight 3x3 multiply in 23 mults + 40 online adds
(vs 42 online by reusing the symmetric record), floor-tight, with
~7.8k distinct schemes attaining the optimum.
