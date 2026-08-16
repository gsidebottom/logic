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

Headline: fixed-weight 3x3 multiply in 23 mults + 40 online adds
(vs 42 online by reusing the symmetric record), floor-tight.
