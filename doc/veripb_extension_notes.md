# VeriPB extension variables — scout notes

Captured during Phase 1.A scouting of `~/projects/veripb/tests/instances/correct/version3/`.
This is the foundation for the Cook-style PHP proofs project.

## How to introduce a fresh variable

Pair of `red` rules with **constant witnesses** (mapping the fresh
var to 0 and to 1):

```
red 1 ~y 1 x1 >= 1 : y -> 0 ;     % adds: y → x1
red 1 y 1 ~x1 >= 1 : y -> 1 ;     % adds: x1 → y
```

Combined: `y ↔ x1` — `y` is now a fresh copy of `x1`.

### Why this is sound

Take `red 1 ~y 1 x1 >= 1 : y -> 0 ;`:

- New constraint C: `~y + x1 >= 1` (= `y → x1`).
- Witness ω: `y → 0`.
- F doesn't contain y (it's fresh).
- F↾ω = F (no y to substitute).
- C↾ω = `~0 + x1 >= 1` = `1 + x1 >= 1` — trivially true.
- The proofgoals are all trivially implied by F. ✓

The witness "y → 0" is a free choice for the fresh variable, and the
substitution makes the new constraint trivially true. Soundness holds
because the new variable's value is unconstrained by F.

After both reds, F is augmented with `y ↔ x1` and y is a usable
fresh variable. Cook-style proofs use this to introduce aux vars
like `y_{p,k} = "pigeon p is in some hole in [1..k]"`.

## How to define `y = (x1 ∨ x2 ∨ ... ∨ xk)`

Triple of red rules:

```
% y → (x1 ∨ ... ∨ xk)
red 1 ~y 1 x1 1 x2 ... 1 xk >= 1 : y -> 0 ;

% xi → y, one per i
red 1 y 1 ~x1 >= 1 : y -> 1 ;
red 1 y 1 ~x2 >= 1 : y -> 1 ;
...
red 1 y 1 ~xk >= 1 : y -> 1 ;
```

Each rule's witness makes its new constraint trivially true under the
substitution, and F is unchanged (y fresh).

## How to define `y = (x1 ∧ x2 ∧ ... ∧ xk)`

Dual:

```
% (x1 ∧ ... ∧ xk) → y, i.e., ~y ∨ ~x1 ∨ ... ∨ ~xk (one clause)
red 1 y 1 ~x1 1 ~x2 ... 1 ~xk >= 1 : y -> 1 ;

% y → xi, one per i
red 1 ~y 1 x1 >= 1 : y -> 0 ;
red 1 ~y 1 x2 >= 1 : y -> 0 ;
...
```

## Worked example from VeriPB tests

`~/projects/veripb/tests/instances/correct/version3/add_preserved_var_subproof.pbp`:

```
red 1 ~x5 1 x1 >= 1 : x5 0 ;     % x5 → x1
core id -1;
red 1 x5 1 ~x1 >= 1 : x5 1 ;     % x1 → x5
core id -1;
```

(The `core id -1` moves the new constraint to the core set so
subsequent rules can reference it without unchecked-deletion issues.)

After both reds, x5 = x1 in the formula. The proof then uses
`preserved_add` to mark x5 as a preserved variable, which is needed
for the formula-preservation argument in optimization contexts but
unrelated to the cardinality use case.

## Application to Cook's PHP proof

Cook 1976 uses aux variables `y_{p,k}` = "pigeon p is in some hole
in [1..k]". The recursion:

```
y_{p,0} = 0  (no hole available below 1)
y_{p,M} = 1  (pigeon must be SOMEWHERE)
y_{p,k} = y_{p,k-1} ∨ x_{p,k}
```

Equivalently: `y_{p,k} ↔ (y_{p,k-1} ∨ x_{p,k})`.

Each such definition can be introduced via 3 red rules (defining
`y_{p,k}` as OR of two terms).

Then the cardinality argument is:

- Sum over p of (y_{p,M} - y_{p,M-1}) = number of pigeons in hole M.
  Derive via pol: this should be ≤ 1 (at-most-1 per hole, derivable
  from mutex once we have the y vars).
- Total pigeons = sum over p of y_{p,M} = N.
- Total pigeons in any hole ≤ 1 implies total ≤ M.
- N > M → ⊥.

The exact pol derivation chain is what Phase 1.B / 1.C need to work
out. The key insight: with y vars, we can express "exactly one hole
per pigeon" as a single PB constraint per pigeon, then aggregate
cleanly.

## Application to RoundRobin

RoundRobin's structure: x_{ij,k} = match (i,j) plays day k.

Pigeon-style: each match plays SOME day. Cook-equivalent aux:
`y_{ij,k}` = "match (i,j) plays some day in [1..k]".

Mutex-style: each team plays ≤ 1 match per day. This is the
double-cardinality layer. Will need additional aux vars:
`z_{i,k}` = "team i plays SOME match on day k" — derived from
mutex via OR over matches involving team i.

Then: total matches = sum over (i,j) of y_{ij,d} = 120.
Total team-day pairs occupied = sum over (i,k) of z_{i,k}.
Each match uses 2 team-days, so total matches × 2 ≤ total team-day
occupations. With z bounded by 1 per (team, day) → ≤ n × d = 208.
So matches ≤ 104. 120 > 104 → ⊥.

The exact derivation is what Phase 3 needs to nail down.

## Open questions to validate in Phase 1.C

1. **Does VeriPB accept ANY fresh variable name?** The docs say
   variable names must be ≥ 2 chars and not contain spaces. So
   `y_p_k`, `y1`, `aux42` should all work. `y_1_2` should too.
2. **Are there limits on how many aux vars we can introduce?**
   Probably not, but VeriPB may have per-instance limits we should
   measure.
3. **Does the order of red-rule additions matter?** Each red is
   independent, so order shouldn't matter for soundness, but it does
   affect ConstraintIDs which subsequent `pol` rules reference.
