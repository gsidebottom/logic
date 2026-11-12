# Tomar's lemma line, part 2: planes, capacities, projected seeds (2026-11-06)

Three follow-ons to the group re-decomposition moves of ../group_moves
(move 1, negative at equal budget), all from Alexandre Sedoglavic's
pointer to Tomar's arXiv:2610.11823 (Lemma 2.1, the quotient/capacity
lemma) and his projection page (the substitution method,
<n,m,p+1:r> -> <n,m,p:r-m> and its transposes):

- **planes** (G3): the subspace re-decomposition move at dimension 3,
  a plane group's partial sum is a 3-slice tensor; probed before wiring
  it into the engine (section 1);
- **move 2**: the lemma's capacities as constraints in the SAT
  completion of a partial scheme (section 2, matmul/capacity.py);
- **move 3**: projection as a seed generator, descending with flips
  from the projections of a larger scheme instead of the trivial
  scheme (section 3, matmul/project_f2.py).

Protocol as in ../group_moves: 12 threads, one 5-minute run per arm,
seed 7, the same binary for every arm, arms back to back on an idle
machine.  The flip engine is unchanged except for the seed-pool start
(`--seeds-dir`, src/bin/flip.rs) and the plane move behind
`--group-moves 4` (off in every arm here).

## 1. Planes (G3): the subspace move at dimension 3

A plane group: the terms of a scheme whose factors in one slot lie in a
3-dimensional subspace spanned by three present factors (7 nonzero
points), 4 to 8 terms.  Its partial sum is a 3-slice tensor; the group
can be rewritten in rho terms iff that tensor has rank <= rho over F2.
src/flip_group.rs:

- lower bound: Tomar's profile argument.  A decomposition with n_y terms
  on point y must give every form f at least rank(S_f) terms with
  f(y) = 1 (S_f the flattening along f, 7 forms) and every point x at
  most r - rank(T mod x) terms on x (T mod x the quotient pencil, 7
  points); the least feasible profile sum is the bound.  Staged from
  cheap to exact: the seven form ranks; then the Kronecker bound on the
  seven quotient pencils (sound, test kronecker_pencil_bound_is_sound_
  at_small_sizes: never above the exact pencil rank on 400 random
  pencils); then the exact brute-force pencil rank where du * dv <= 16.
  The unstaged bound (brute force on every group) cost 200 ms per
  group and 576 s for one <3,3,4> state (planes/timing1.log); staged,
  18 ms per state (planes/timing2.log), because the form ranks alone
  close almost every group.
- witness: a greedy decomposition in each of the 28 dual bases of the
  plane (pure slices plus shared rank-ones lowering two or three slices
  at once, exact rank-one tests), cost = sum of the seven part ranks.
  On 300 random groups the bound equals the greedy (total gap 0,
  plane_bound_below_greedy_and_parts_reproduce); planted shared
  rank-ones are found (planted_shared_rank_one_is_found).
- exact decision: for a group the bound leaves open and the greedy does
  not reduce, the probe writes "rho = k - 1 terms" as CNF (Tseitin
  products and XOR chains per tensor entry) and asks CaDiCaL 3.0.0
  (10 s cap); a witness is checked against the tensor and the
  rewritten scheme against Brent before it counts.
- engine move `--group-moves 4` (plane_reduce, validity test
  plane_rewrites_preserve_validity: 6 rewrites + 2 reductions on
  flipped 3x3 schemes, all Brent-checked).  Not run in any A/B: the
  probe below says why.

Probe (src/bin/group_probe.rs, the move-1 states: <3,3,4> 1386 at
29-30, <4,4,4> 2928 at 49-56): per state, `base` = guided_descend
without the moves (3 tries x 100,000 flips), the G1/G2 arms as before,
`plane` = greedy on every open group, `planesat` = SAT on the rest
(24 calls per state at most), the first lowering of each kind applied
to a copy and Brent-checked.  Logs planes/probe334_planes2.log,
planes/probe444_planes2.log (stopped at 1600 states, statistics only),
planes/probe444_planes3.log (a seeded 1000-state sample with the
cross-tab), planes/probe444_planes4.log (a full run at background priority
beside the climb, timed out at 1200 states, statistics only),
planes/probe444_planes5.log (the full run at normal priority, all
2928 states, with the cross-tab: the result of record),
planes/probe444_planes6.log (a second full run, seed 8, naming its
GROUP ONLY states), planes/probe444_gonly50.log (base with 50 tries on
the two named states).

| format | plane groups (k = 4 / 5 / 6 / 7 / 8) | closed by the bound | open | reduced by the greedy | SAT calls: reduced / unsat / unknown |
|---|---|---|---|---|---|
| <3,3,4>, 1386 states, 227 s | 2,447,655 (2,005,373 / 383,289 / 53,083 / 4,293 / 1,617) | 2,359,591 (96.4 %) | 88,064 | 88,063 | 1: 1 / 0 / 0 |
| <4,4,4>, first 1600 states, 1749 s | 11,220,341 | 10,355,081 (92.3 %) | 865,260 | 863,855 | 1,276: 184 / 1,056 / 36 |
| <4,4,4>, 1000-state sample, 3556 s | 9,550,875 (7,996,028 / 1,310,838 / 204,868 / 33,067 / 6,074; 918 with k > 8) | 8,589,699 (89.9 %) | 961,176 | 960,406 | 680: 124 / 506 / 50 |
| <4,4,4>, all 2928 states, 6141 s | 28,524,132 (23,888,746 / 3,909,544 / 613,466 / 96,868 / 15,508; 2,138 with k > 8) | 25,567,277 (89.6 %) | 2,956,855 | 2,954,526 | 2,030: 411 / 1,470 / 149 |

At <3,3,4> the bound is exact on every plane group of every state:
closed means irreducible, open means the greedy (once SAT) rewrites it.
At 4x4 it is not: over all 2928 states 1,470 open groups are UNSAT at
k - 1, the greedy misses 411 reducible groups that SAT finds, and 149
SAT calls are undecided at the 10 s cap (the 1000-state sample: 506 /
124 / 50; no state reached the 24-call cap in any run).  The groups are
not rare (every state carries them; 3.6 % are reducible at <3,3,4> and
10.4 % at 4x4), and the question is whether any opens a state the
baseline cannot open:

| states | lowered by base | group alone | shuffles+group | plane greedy | plane SAT | base vs any group move (G1/G2, shuffles, planes): both / base only / GROUP ONLY / neither | plane greedy only | plane SAT only |
|---|---|---|---|---|---|---|---|---|
| <3,3,4>, all 1386 | 671 | 290 | 466 | 441 | 1 | 502 / 169 / **0** / 715 | 0 | 0 |
| <4,4,4>, 1000-state sample | 802 | 587 | 649 | 704 | 124 | 723 / 79 / **0** / 198 | 0 | 0 |
| <4,4,4>, all 2928 | 2379 | 1790 | 1975 | 2126 | 411 | 2168 / 211 / **1** / 548 | 1 | 0 |
| <4,4,4>, all 2928, second run (seed 8) | 2384 | 1790 | 1978 | 2126 | 411 | 2170 / 214 / **2** / 542 | 2 | 0 |

Mean time per <3,3,4> state: base 49 ms, one group scan 0.2 ms, 200
shuffles 31 ms, planes (bound, greedy, SAT) 1763 ms; per 4x4 state in
the full run at normal priority: base 19 ms, group 0.3 ms, shuffles 40
ms, planes 24.5 s (2.96 M open groups through the greedy and 2030 SAT
calls at 1.2 s each; the sample on the efficiency cores: 39 ms, 0.6 ms,
73 ms, 40.7 s).  That is the other reason the move is not wired into a
timed arm: a plane scan costs 35 base scans at <3,3,4> and 1000-1300 at
4x4.

Verdict: NEGATIVE at both formats.  At <3,3,4> the plane move lowers
441 of 1386 states (one of them through SAT) and every one of them is
lowered by the base engine too.  At 4x4, over all 2928 states
(planes/probe444_planes5.log, 102 min at normal priority), the plane
greedy lowers 2126 states and SAT 411 more, the base engine lowers
2379, and the cross-tab is both 2168 / base only 211 / GROUP ONLY 1 /
neither 548 (plane-only 1, SAT-only 0): one state in 2928 was lowered
by the plane greedy and by none of base's three tries, the group scan
or the shuffles.  That one is inside the arms' own noise: the base arm
and the guided+moves arm are the same descent with different random
streams, and they disagree on 61 states (35 lowered by guided+moves
and not by base, 26 the other way).  A second full run (seed 8,
planes/probe444_planes6.log, 97 min) repeats the deterministic arms
exactly (group 1790, plane greedy 2126, plane SAT 411, the same 28.5 M
groups), draws base 2384 and the cross-tab 2170 / 214 / GROUP ONLY 2 /
542, and names its two GROUP ONLY states: r55-00014 (plane greedy
only) and r55-00113 (plane greedy and guided+moves).  Given 50 tries
instead of 3, base lowers both (planes/probe444_gonly50.log): the
GROUP ONLY states are base's sampling noise at 3 tries, not states the
plane move alone can open.  The reducible plane groups are real and
common (2.95 M of the 2.96 M groups the bound leaves open rewrite in
k - 1 terms, a tenth of all plane groups at 4x4), but every rewrite
that lowers the rank sits in a state flips and merges lower anyway;
the 149 SAT calls (of 2030) that timed out are the only undecided
groups.  The seeded 1000-state sample
at background priority (planes/probe444_planes3.log: 723 / 79 / 0 /
198) and an earlier full run at background priority beside the climb
that timed out after 4 h at 1200 states (planes/probe444_planes4.log,
statistics only) agree with the full run.

## 2. Move 2: capacities as constraints in SAT completion

Tomar's Lemma 2.1 in our terms (matmul/capacity.py): for a rank-r
scheme of <n1,n2,n3> and a nonzero linear form f on one slot's space,
the terms with f(factor) = 1 number at least m_X * rank f, where m_X is
the dimension the slot's matrices are multiplied against (n3 for a, n1
for b, n2 for c); this is unconditional (the image of the tensor modulo
ker f is f^T (x) I).  And at most r - R(T_S) factors lie in a subspace S
of row or column type, R(T_S) the rank of the smaller format the quotient
leaves; these capacities rest on lower bounds for the smaller formats,
taken from a table with provenance (Hopcroft-Kerr 1971 <2,2,n> = ceil(7n/2)
and <2,3,3> = 15 over F2; <2,3,4> >= 19, Hopcroft-Kerr's sketch completed
by Wang 2026, arXiv:2603.07280; <3,3,3> >= 20, Wang 2026, verified;
<1,m,p> = mp; closure R(<n,m,p+1>) >= R(<n,m,p>) + m and the transposes).
`capacity.py report` finds 0 violations on AlphaTensor's <3,3,4>:29 and
3x3:23 and tight constraints on both, so the constraints have teeth on
real schemes.

Instances: `capacity.py cnf` writes the Brent equations of a completion
(one slot frozen to a known scheme's factors, the other two free; or a
few terms dropped from a known scheme) with optional cardinality
constraints by Sinz's sequential counters: `entries` (the form counts
on the free slots), `caps` (the subspace capacities, a selector z per
term and at_most(z, r - LB)), `all` (both).  SAT instances i1 (<3,3,4>
r = 29, a frozen to AlphaTensor's 29) and i2 (3x3 r = 23, a frozen);
i3 (<3,3,4> r = 28: term 0, or term 7, dropped from the 29 and the a
slot frozen to the remaining 28 factors; a solution would be a rank-28
scheme, below the record, so UNSAT is expected and the instance
measures refutation time); i4 (4x4 r = 47, a frozen to AlphaTensor's
47: SAT in principle, it measures the scale).  i1 `none` has 13,512
variables and 48,384 clauses, i1 `all` 199,448 / 460,822; i4 `all`
1,083,338 / 2,423,250.  CaDiCaL 3.0.0, 600 s cap, two seeds, 8 in
parallel on an otherwise idle machine (caps/run_move2.sh, table by
caps/summarize_move2.py).

Round 1 (caps/logs/m2_chain.log; 8 jobs in parallel, so each
instance's variants ran together under equal load; seconds for seeds 1 / 2):

| instance | none | entries | caps | all |
|---|---|---|---|---|
| i2: 3x3 r = 23, a frozen (SAT) | SAT 48 / 21 | SAT 35 / 13 | SAT 37 / 43 | SAT 12 / 46 |
| i1: <3,3,4> r = 29, a frozen (SAT) | > 600 / > 600 | > 600 / > 600 | > 600 / > 600 | > 600 / > 600 |
| i3: <3,3,4> r = 28, term 0 dropped (UNSAT expected) | > 600 / > 600 | > 600 / > 600 | > 600 / > 600 | > 600 / > 600 |
| i3: <3,3,4> r = 28, term 7 dropped (UNSAT expected) | > 600 / > 600 | - | - | > 600 / > 600 |
| i4: 4x4 r = 47, a frozen (SAT) | > 600 | - | - | > 600 |

The one instance CaDiCaL solves it solves in 12 to 48 s under every
variant, the spread between seeds (21 against 48 s for `none`) as wide
as the spread between variants; every harder instance is censored at
600 s with and without the constraints.  Round 2 (caps/run_move2b.sh,
instances between those two sizes: 3x3 r = 22 with a term dropped,
<2,3,4> r = 20 a frozen, <2,3,4> r = 19 with a term dropped, where 19 is
Wang's lower bound and 20 the record, so a model would be a discovery):

| instance (round 2, caps/logs/m2b_chain.log; background priority beside the orbit scan, so absolute times are inflated, the variants of one instance ran together) | none, seeds 1 / 2 | all, seeds 1 / 2 |
|---|---|---|
| i5: 3x3 r = 22, term 0 dropped (UNSAT) | UNSAT 29 / 28 s | UNSAT 102 / 101 s |
| i5: 3x3 r = 22, term 11 dropped (UNSAT) | UNSAT 62 / 50 s | > 600 / UNSAT 84 s |
| i6: <2,3,4> r = 20, a frozen (SAT) | > 600 / > 600 | > 600 / > 600 |
| i7: <2,3,4> r = 19, term 0 dropped (open) | > 600 / > 600 | > 600 / > 600 |

The refutations are the informative case: with the capacities and
form counts added (6,147 -> 19,381 variables, 21,951 -> 50,871 clauses)
CaDiCaL takes 2 to 3.5 times longer to refute, and one of four
constrained jobs is censored where every plain job finishes.  The
constraints are implied facts the solver would have to rediscover, and
encoding them as sequential counters costs more propagation than the
pruning returns, at least at this scale and in this encoding.

Verdict: NEGATIVE.  The capacities are true and tight on real schemes
(0 violations, several at equality on AlphaTensor's <3,3,4> and 3x3),
but as cardinality constraints in the completion CNF they do not solve
anything CaDiCaL cannot solve without them (i1, i3, i4, i6, i7 censored
on both sides) and they slow the one refutation it can do (i5).  Not
tried: the caps as a symmetry-breaking or branching order rather than
as clauses, or a native pseudo-Boolean solver.

## 3. Move 3: projected seed pools against the trivial start

Seeds: AlphaTensor's F2 schemes of the next format up
(matmul/external/alphatensor_f2, tensor-checked on conversion),
projected by matmul/project_f2.py: a basis change puts the killed
direction last, the killed variables are substituted so that q products
vanish with independent restricted forms, the killed outputs dropped;
every projection is checked against the smaller tensor (0 failures).
Pools (proj/make_pools.sh; 40 bases per direction for the ref47 pool,
20 otherwise):

| target | source (mode) | seeds at rank |
|---|---|---|
| <3,3,4> | <3,3,5>:36 (col, 36-3), <3,4,4>:38 (inner-a 38-3, inner-b 38-4) | 533 at 33, 901 at 35, 1500 at 34 (2934 in all) |
| <4,4,4> | <4,4,5>:63 (col, 63-4) | 1500 at 59 |
| <4,4,4>, overnight run | <4,4,5>:63 (col) and its two other orientations <4,5,4>:63 (inner-a, inner-b) and <5,4,4>:63 (row), by matmul/rotate_f2.py | 4 x 1500 at 59 (6000) |
| <3,4,4> | <3,4,5>:47 (col, 47-4), the three published 4x4 47s (row, 47-4) | 1500 + 600 + 600 + 593 at 43 (3293) |
| <4,4,4>, Kauers-Moosbauer parent (2026-11-07 evening) | <4,4,5>:60 over F2 (their flips repository; ../external/km_flips) by col, and its rotations <4,5,4> by inner-a and inner-b and <5,4,4> by row (proj/make_km_pools.sh) | 4 x 1500 at 56 (6000) |
| <4,4,4>, AlphaEvolve parent (2026-11-08 evening) | <4,4,5>:61 over Z reduced mod 2 (Perminov's collection, alpha_evolve/4x4x5_m61_mod0.json; ../external/ae445, matmul/json_to_bits.py) by col, and its rotations by inner-a, inner-b and row (proj/make_ae_pools.sh) | 4 x 1500 at 57 (6000) |
| <4,4,4>, Moosbauer parent (2026-11-09 afternoon) | <4,4,5>:62 over Z reduced mod 2 (his flips repository via Perminov's collection, jakobmoosbauer_flips/445-62-mod0.exp; ../external/mb445, matmul/exp_to_bits.py reading integer coefficients) by col, and its rotations by inner-a, inner-b and row (proj/make_mb_pools.sh) | 617 + 617 + 1500 + 601 at 58 (3335) |

The recipe regenerates six pools exactly; the two capped pools
(<4,4,5> -> 4x4, at47 -> <3,4,4>) come back with 1416/1500 and 580/600
of the A/B's files (the cap truncates in hash order; PYTHONHASHSEED is
pinned now).  Each `--seeds-dir` run Brent-verifies every seed at its
rank, starts each trajectory from a random seed of the pool, and the
collector Brent-verifies every landing before writing it.

| arm | record | first at record | distinct landings at record / record+1 | landings | trajectories | diffusion flips | distinct types at record |
|---|---|---|---|---|---|---|---|
| <3,3,4> trivial (36) | 29 | 29 at 2 s | 1507 / 5222 | 9402 | 6227 | 81.5 M | 385 |
| <3,3,4> projected (2934 at 33..35) | 29 | 29 at 0 s | 1483 / 6425 | 11962 | 6558 | 78.9 M | 324 (269 shared, 55 new, 116 only trivial) |
| <3,4,4> trivial (48) | 38 | 38 at 17 s | 3046 / 5728 | 11130 | 7659 | 99.8 M | 185 |
| <3,4,4> projected (3293 at 43) | 38 | 38 at 0 s | 5033 / 5786 | 11137 | 6830 | 82.5 M | 1459 (3 shared) |
| <4,4,4> trivial (64) | 47 | never: 54 at 64 s, nothing below in 5 min | 0 / 0 (nothing at or below 49) | 0 | 128187 | 2056 M | - |
| <4,4,4> projected (1500 at 59) | 47 | **47 at 0 s** | **5 / 4721** (and 4356 at 49) | 15985 | 6819 | 81.7 M | 3 |

"Type" = the multiset over terms of (rank a, rank b, rank c), sorted
inside the triple on the square format (an invariant of the de Groote
class under sandwiching and the S3 symmetries; proj/scheme_types.py).
No landing is shared between the two arms of any pair (different
starts), so the comparison is by type.

- <3,3,4> and <3,4,4>: both starts reach the record within seconds, no
  28 and no 37.  The projected pools land in a different part of the
  record level: at <3,4,4>, 1459 types against 185 with 3 in common;
  at <3,3,4>, 324 against 385 with 269 in common.  The trivial start
  funnels into few types at <3,4,4>; the projections do not.
  A 30-minute seeded <3,4,4> run aiming at 37 (seed 11, 12 threads,
  proj/logs/m3_344_proj30.log): no 37; 23,175 distinct 38s and 35,112
  distinct 39s from 41,044 trajectories.  Its trivial-start control
  (same budget and seed, proj/logs/m3_344_triv30.log, run the next
  morning with the 4x4 descent's last 13 minutes still on the
  efficiency cores): no 37 either; 25,372 distinct 38s and 39,473 39s
  from 50,552 trajectories.  At <3,4,4> the seeds buy nothing toward
  37: both starts sit on the 38 level within seconds and the half hour
  is spent enumerating it.
- <4,4,4>: from the trivial scheme the engine stalls at 54 (128 k
  trajectories, none at 49 or below), from the projections of
  AlphaTensor's <4,4,5>:63 every worker is at 47 within the first
  second and 15985 landings at 47..49 follow in 5 minutes (2.3 per
  trajectory).  No 46.  The earlier baseline run from the trivial
  scheme (../group_moves, same seed, the binary before the seed-pool
  change) reached 49 once at 211 s in 92 k trajectories, so the
  trivial start's reach in 5 minutes is itself a lottery; the
  projected start is not.  Replicate (seed 8, 2 min per arm,
  proj/run_m3_rep.sh, logs proj/logs/m3rep_*): trivial 54 at 64 s and
  nothing at or below 49 in 51 k trajectories; projected 47 at 0 s,
  then 2 distinct 47s, 2050 48s and 1749 49s in 2 minutes.  One of the
  two 47s is r47-00001 again, term for term; the other carries
  Kauers-Moosbauer's type like r47-00004.  Overnight (seed 13, 3 h at
  background priority on the efficiency cores beside the climb, all four
  projection pools = 6000 seeds at 59 including the two other
  orientations of <4,4,5>:63 made by matmul/rotate_f2.py; proj/run_d180.sh,
  log proj/logs/m3_444_proj180.log): 65,162 landings from 28,498
  trajectories, 22 distinct 47s (proj/found47_d180), 13,757 48s, 18,198
  49s, no 46.  By type 9 are AlphaTensor-like, 8 Kauers-Moosbauer-like
  and 5 carry the new class's type; four of the 22 are r47-00001..4
  again, term for term, none is r47-00005.  The exact equivalence test
  (proj/scheme_iso.py: a term bijection consistent with the factor-rank
  signatures, the pair ranks and F2-linearity, then the slot maps
  M -> P M Q read off and re-verified, over every slot-symmetry variant
  of the second scheme; exact both ways, self-tested on random
  sandwiches) puts all five in proj47_5's class.  Over all 30 rank-47
  schemes we hold (the three published, the five from the 5-minute
  runs, the 22 from the descent) there are exactly four de Groote
  classes: AlphaTensor's (13 schemes, 12 of them ours),
  Kauers-Moosbauer's (10, 9 ours), the projection-descent class (6, all
  ours) and AlphaEvolve's (walkseeds/ref47 alone; no descent reached
  it); proj/logs/iso47_classes.log, 2 s for the 30.  (A fifth class
  appeared the next night from the Kauers-Moosbauer parent pool; see the
  2026-11-07 evening bullet below.)
  The pairwise and triple factor-sum rank invariants
  (proj/class_invariants.py, proj/logs/class_invariants.log) split the
  30 into the same four groups as the type does.
- The five 47s (proj/found47, each re-checked against the tensor and
  all 256 basis-matrix products, proj/logs): three carry AlphaTensor's
  type profile, one Kauers-Moosbauer's, one matches none of the three
  published 47s (matmul/x47/walkseeds), so it is a fourth class
  relative to our seeds (the invariant is preserved by GL(4,2)^3 and
  the slot symmetries, so a different value proves inequivalence; the
  same value would not prove equivalence, which proj/scheme_iso.py now
  decides exactly; and Kauers-Moosbauer's flip-graph paper reports over
  100,000 rank-47 schemes over F2 without a class count).  All five, like the three published ones,
  are flip-isolated: no two products share a factor, so plain flips
  cannot leave them, which is why descents from different seeds end
  in different classes.  XOR count of the new class (matmul/x47,
  `seeds/proj47_5`): as given 46 + 46 + 88 = 180 under Boyar-Peralta;
  24 annealed orbit chains end at 171 (22 chains), 172 and 173, best
  45 + 45 + 81, where the three published classes' chains all end at
  168; the cheap stage of the whole-orbit lower bound gives >= 151
  (the published class gave 148 there and climbed to 160, AlphaTensor's
  152).  The exhaustive BP orbit scan (all 840^3 coset triples, 63 min
  on 12 threads shared with the probe) confirms the plateau: orbit
  minimum 171 under BP against 168 in each published class, 411 triples
  within +2 as collected (52 at 171; the collection missed 235 of the
  646 within +2, see below).  The exact refine of the 411 triples gives
  171 (44 + 45 + 82 at the best triple; both input sides exact, the
  product side 51 against a bound of 50 through its transpose), and
  settling at depth 5 (57 min) proves eight triples exactly 171 and
  leaves 78 of the 411 open below 171; depth 6 (20 min, a 1200 s cap
  per helper level) settles 28 more sides exactly and leaves 57 points
  open below 171 through six distinct sides at 6 to 8 helpers; depth 8
  (48 min, cap 2400 s) settles 40 more sides exactly (eight of them one
  below BP) and leaves one point open: total 173, bound 170, through
  the one side that times out at every cap (43 targets, BP 50, bound
  47).  The bottom-up pass added to settle for that side (after the
  top level's 2400 s timeout it climbs from level 0; out/settle8b)
  refutes levels 0 to 5 in two seconds, so the side costs 49 or 50 and
  the point is at least 172: all 411 collected candidates are settled
  and eight triples reach 171.  Caveat found the same afternoon: the
  scan kept a per-X candidate list that it cleared whenever a lower
  per-X best appeared, dropping triples still within the window, so the
  411 are 411 of the 646 triples within +2 (the minimum itself and the
  52 triples at 171 are unaffected).  Fixed (scan keeps what is still
  within the window; `--tables` re-emits candidates from the saved side
  tables); the +4 window, 7698 triples including all 646, was
  refined and settled from the saved tables (2026-11-07 18:00 to 2026-11-08
  13:31, Q6b and Q7, all four classes): km47 167 exact over its 1824
  triples, at47 168 exact over 3844, this class 171 exact over 7698, and
  ref47 168 with 30 of 2882 triples open only through the published
  scheme's own output side (34 targets, BP 49, floor 39, 14 helpers to
  decide); matmul/x47/README.md.  The climb of the whole-orbit lower bound
  (matmul/x47 lbclass.sh) proves every orbit point costs at least 163:
  152-162 in 6.5 h, then the 163 step in 7.3 h over two runs (a 12,600 s
  budget run, 13,389 s, levels 3-4 in five minutes and eleven level-5
  refutations of 17-27 min each, stopped with 6 coset triples open on
  one side; resumed from the shared checkpoint with a 21,600 s budget and
  a 5400 s cap per level test, 12,787 s: five more level-5 refutations,
  one level-6 timeout at the cap, and a level-7 refutation closing the
  last triples).  Windows, bound to best known point: this class 163-171,
  the published class 160-168, AlphaTensor's 162-168, Kauers-Moosbauer's
  163-167.  A point below 167 would need four XORs of exact gains over
  the BP counts across three sides, where the KM class gave one.

- Parent pool from Kauers-Moosbauer's <4,4,5>:60 (2026-11-07 evening;
  matmul/external/km_flips, the one <4,4,5> scheme their flips repository
  publishes, converted and Brent-checked by matmul/exp_to_bits.py): one
  projection drops 4, so the seeds sit at 56 against 59 from AlphaTensor's
  63; four orientations by rotate_f2.py, 1500 seeds each
  (proj/make_km_pools.sh, 0 failed checks).  Equal-budget arms beside the
  running orbit-window queue (5 min, 12 threads, seed 7, the 2026-11-06 flip
  binary, both arms under the same load): the 56 pool (col, 1500) lands at
  47 at 0 s and gives 2 distinct 47s, 2760 48s and 2670 49s from 9319
  landings in 3339 trajectories; the 59 pool rerun gives 3 / 2767 / 2382
  from 8733 landings in 3735 trajectories (both at half of yesterday's
  idle-machine throughput).  No 46.  Classes (proj/scheme_iso.py): both 47s
  from the 56 pool are in Kauers-Moosbauer's class, the three from the 59
  pool in AlphaTensor's (2) and the projection-descent class (1); logs
  proj/logs/m3_444_km56_col.log and m3_444_at59_col_rerun.log, the two 47s
  in proj/found47_km56.  The 3 h descent from all 6000 seeds at background
  priority (seed 13, as the overnight run; 21:10-00:10, 91,931 reductions,
  58,199 landings in 22,740 trajectories, proj/logs/d180_444_km56.log)
  wrote 14 distinct 47s, 15,126 distinct 48s and 17,768 49s, no 46.  The
  47s, each re-checked against all 4096 Brent equations (proj/brent_bits.py,
  pure Python, both gamma conventions tried), sort into THREE classes
  (proj/scheme_iso.py, proj/logs/iso_d180_km56.log): Kauers-Moosbauer's 5,
  the projection-descent class 6, and a FIFTH class of 3 (r47-00007, -13,
  -14, written at 21:15, 22:55 and 23:21) that matches none of the four
  known ones.  The rank-triple type alone separates it (per-slot counts of
  factors of rank 1/2/3: a 20/11/16, b 11/27/9, c 20/11/16, no rank-4
  factor; proj/class_invariants.py), so the verdict does not rest on the
  exhaustive search.  All 14 are in proj/found47_km56/d180; the fifth
  class's representative is matmul/x47 `seeds/projkm47_7` (as given 46 +
  56 + 77 = 179 under Boyar-Peralta), whose +4 orbit-window scan the next
  morning gave the NEW XOR RECORD 166 (two orbit points, 44 + 48 + 74 and
  43 + 48 + 75, all sides exact, x47check.py and PLinOpt's SLPchecker;
  matmul/x47/best/x166 and its README), one below the Kauers-Moosbauer
  class's 167 of October.  The projection pool from the <4,4,5> parent is
  what found the class that holds the record.  A replicate of the 3 h
  descent (seed 17, 2026-11-08 13:15-16:15, background priority beside the
  settle queues; 71,619 reductions, 45,302 landings in 17,751 trajectories,
  proj/logs/d180b_444_km56.log) wrote 16 distinct 47s (two of them files of
  the first run), 13,102 48s and 13,765 49s, no 46; all 16 Brent-checked;
  classes (proj/logs/iso_d180b_km56.log): Kauers-Moosbauer's 7, the
  projection-descent class 7, the fifth class 1, and for the first time
  from this parent AlphaTensor's 1.  No sixth class.  Files in
  proj/found47_km56/d180b.

- Parent pool from AlphaEvolve's <4,4,5>:61 (2026-11-08 evening;
  matmul/external/ae445, the Z scheme of Perminov's collection reduced mod
  2 by matmul/json_to_bits.py, all 61 products surviving, Brent-checked):
  seeds at 57, four orientations, 1500 each, 0 failed checks
  (proj/make_ae_pools.sh).  NEGATIVE: the 3 h descent (seed 13, 12
  threads, beside the lns search of lane B; proj/logs/d180_444_ae57.log)
  made 444,282 reductions in 133,198 trajectories and 1.59 G diffuse flips,
  reached rank 51 within 44 s, and never went below 51: no landing at 49,
  nothing written.  The AlphaTensor parent (seeds at 59) and the
  Kauers-Moosbauer parent (56) both reach 47 at 0 s from the same kind of
  pool, so the parent, not the seed rank, decides where the funnel ends;
  the AlphaEvolve projections sit in a basin whose floor is 51.  The seeds
  are not flip-isolated (5-7 shared-factor pairs per seed, against 15-27
  for the Kauers-Moosbauer pool); the engine was working the whole time.

- Parent pool from Moosbauer's <4,4,5>:62 over Z (2026-11-09 afternoon;
  matmul/external/mb445, the integer flip-graph scheme of Perminov's
  collection reduced mod 2 by matmul/exp_to_bits.py, which now reads
  integer coefficients and drops the products that vanish mod 2: none do,
  rank 62, Brent-checked): seeds at 58, four orientations, 3335 seeds in
  all (proj/make_mb_pools.sh, 0 failed checks).  NEGATIVE at a floor of
  49: the 200-minute descent on 4 threads (seed 1, 13:41-17:01 beside the
  ten long-cap SAT arms; proj/logs/d200_444_mb58.log) made 335,831
  reductions in 93,113 trajectories and 1.15 G diffuse flips, was at 49
  within 0.3 s and never below: 74,554 landings, 5,455 distinct 49s, no
  48, nothing written.  The four <4,4,5> parents sit at three floors:
  AlphaTensor's 63 and Kauers-Moosbauer's 60 reach 47 within a second,
  Moosbauer's 62 stops at 49, AlphaEvolve's 61 at 51.  The remaining
  parents are two projections away (Moosbauer's <4,5,5>:76 and <4,4,6>:74
  over Z, the catalog's meta_flip_graph <4,4,6>:73 with coefficients in
  thirds, all reduced mod 2 by matmul/m_to_bits.py into
  matmul/external/mb455 and mb446; proj/make_mb2_pools.sh builds the
  two-step pools, inner + col in both orders for <4,5,5>, col + col for
  <4,4,6>) and are probed at the Kauers-Moosbauer reference budget; see
  the next bullet.

- Parents two projections away (2026-11-09 evening; matmul/external/mb455
  and mb446: Moosbauer's <4,5,5>:76 and <4,4,6>:74 over Z and the catalog's
  meta_flip_graph <4,4,6>:73 with coefficients in thirds, all reduced mod 2
  at full rank by matmul/m_to_bits.py and Brent-checked).  Pools by
  proj/make_mb2_pools.sh (every projection tensor-checked, each pool
  deduplicated by content; proj/logs/make_mb2_pools_2026-11-09.log): the
  <4,5,5> by inner-a / inner-b then col and by col then inner-a / inner-b,
  40 stage-1 projections per mode and 25 (or 12 per inner mode) per
  stage-1 seed, 2960 seeds at 67 and 68 (the probe ran on the first
  build's 2480 seeds, three of the four paths: a variable-scoping bug in
  the collector, fixed since, had skipped the col-then-inner-b path); the
  two <4,4,6> by col twice, 1000 seeds at 66 and 1000 at 65.  All three
  NEGATIVE at a floor of 49: the 20-minute 12-thread probes (seed 1,
  17:10-18:10; the Kauers-Moosbauer reference is 47 within 5 minutes at
  this budget; proj/logs/d20_444_mb455_67.log, d20_444_mb446_66.log,
  d20_444_meta446_65.log) reach 49 within a second and never 48: 24,363 /
  24,056 / 23,983 landings, 6,358 / 6,770 / 7,649 distinct 49s, 131-133 k
  reductions each, nothing written.  Seven catalog parents, three floors:
  AlphaTensor's <4,4,5>:63 and Kauers-Moosbauer's <4,4,5>:60 give 47 at
  once; Moosbauer's 445-62, 455-76 and 446-74 and the meta_flip_graph
  446-73 give 49; AlphaEvolve's 445-61 gives 51.  The catalog holds no
  other scheme one or two projections from <4,4,4>, so further parents have
  to be made: see the walk-parent bullet.

- Walk-made parents (2026-11-09 evening, 18:12-19:37; the flip engine's walk
  mode in <4,4,5> with the new `--max-new` cap and `--thin` sampler in
  src/bin/flip.rs and src/flip.rs: that level is far from flip-isolated and
  would flood the archive, 30,000 distinct landings arrive in 9-10 s;
  proj/walkparent_pipeline.zsh).  From Kauers-Moosbauer's 60 and
  AlphaTensor's 63: the first 300 distinct excursion landings ("near", from
  1703 and 2688 landings) and every 100th of 30,000 ("far"), each walked
  scheme projected by col into 10 seeds (3000 seeds at 56 or 59 per run, 0
  failed checks), a 20-minute 12-thread descent (seed 1), the 47s
  class-sorted against the five representatives (proj/logs/walk445_*.log,
  d20_444_walk_*.log, iso_walk_at63_*.log).  NEGATIVE for new classes, and
  the Kauers-Moosbauer neighbours lose the 47: KM near reaches 48 once (at
  4 s) with 11,463 distinct 49s, KM far 48 once (at 721 s) with 6,393 49s,
  no 47 in either; AT near 47 at 0 s, one distinct 47, 13,286 48s and
  18,112 49s; AT far 47 at 0 s, one distinct 47, 13,430 48s and 18,140 49s;
  both AT 47s in AlphaTensor's own class (proj/found47_walkparents).
  Against the parents themselves (47 at 0 s and 2-5 distinct 47s in 5
  minutes from 1500 seeds), the walked parents are an order of magnitude
  weaker or lose the level: 47-adjacency is a property of the specific
  parent scheme, carried along the AlphaTensor walk (its 63 keeps a 47 in a
  form the flips do not touch) and destroyed on the Kauers-Moosbauer one.
  Controlled flip distances next (proj/flipk_f2.py: K random flips, a
  Brent-checked mutation operator at a chosen distance, since the walk
  mode only returns excursion landings; KM's 60 has 10 flippable pairs, AT's
  63 has 29).

- 47-adjacency against flip distance (2026-11-09 19:39-20:15;
  proj/pspace/decay.zsh, pscore.zsh, summarize.py; logs
  proj/logs/decay_{km60,at63}_2026-11-09.txt, *_summary.txt,
  iso_decay_*.log).  Score of a <4,4,5> parent: project it by col into 60
  seeds and descend 6 seconds on 12 threads; both parents score 47 under
  three descent seeds (calibration).  Twenty mutants at each of the flip
  distances 1, 2, 4, 8, 16, 32, 64, 128 (proj/flipk_f2.py, seeds k*1000+m):
  from Kauers-Moosbauer's 60, 159 of 160 mutants still reach 47 within the
  6 seconds (the one miss, distance 32, stops at 49) and all 162 rank-47
  schemes collected are in Kauers-Moosbauer's class; from AlphaTensor's
  63, 160 of 160 reach 47 and all 163 are in AlphaTensor's class (exact
  class sort against the five representatives, no UNDECIDED).  So the
  whole flip neighbourhood of a parent, out to 128 flips, projects onto
  the parent's own 4x4 class, while the walk mode's excursion landings
  (one plus-transition and a reduction, hence another component of the
  rank-60 level) lose the 47 altogether.  The class of the children is a
  property of the parent's flip component.  NEGATIVE for new classes;
  nothing to redo here.

- Parents of our own, option 1 (Greg, 2026-11-09 20:08; proj/own445_pipeline.zsh,
  proj/logs/own445_2026-11-09.txt).  The flip engine descends <4,4,5> itself:
  from 200 projected seeds at 69-72 (the catalog's <4,4,6> and <4,5,5>
  schemes one projection up) it is at 63 in 5 s and in 20 minutes on 12
  threads writes 18,719 distinct 63s and 19,206 64s, nothing at 62
  (proj/logs/d20_445_from_proj69-72.log); from the trivial 80-product
  scheme it reaches 75 in 12 s and no further in 10 minutes
  (d10_445_trivial.log; the engine's landing counters only start at
  --save-at, so its DONE line says 80).  The lowest 300 (all at 63)
  projected by col into 3000 seeds at 59; their 20-minute descent
  (d20_444_own445_59.log) reaches 49 in 2 s and never 48: 5,585 distinct
  49s, nothing written.  NEGATIVE: our own rank-63 <4,4,5> schemes sit in
  components with floor 49, like the catalog's Moosbauer-family parents.

- Parents of our own, option 1b (2026-11-09 21:06-21:47; proj/embed445.py,
  proj/own445b_pipeline.zsh, proj/logs/own445b_2026-11-09.txt).  Each of the
  five class representatives embedded as a <4,4,5> of rank 63, its 47
  products plus the 16 trivial ones of the fifth column (AlphaTensor's 63
  has this shape).  The five together descend in <4,4,5> to 60 within 10 s
  and in 20 minutes give 15,800 distinct 60s, 15,748 61s and 12,563 62s
  (d20_445_from_embedded63.log), so rank-60 <4,4,5> schemes are plentiful
  from this construction.  300 of the 60s, projected by col into 3000 seeds
  at 56 (the Kauers-Moosbauer pool's rank), descend to 47 at 0 s but give
  one distinct 47 in 20 minutes, 10,010 48s and 16,353 49s
  (d20_444_own445b_56.log), and the 47 is in Kauers-Moosbauer's class
  (iso_own445b.log; proj/found47_walkparents/own445b_r47-00001).  No new
  class.  The parents' provenance by class is not tracked by the engine;
  per-class embedding descents would tell whether each class's 60s project
  back to their own class, as the flip-component picture predicts.

- k-subset re-solve, option 4 (Greg, 2026-11-09 20:30, before any lower-bound
  work).  src/bin/kres.rs enumerates every k-subset of a 47's products whose
  sum R can have rank below k, by the flattening ranks: the c-flattening of
  R has rank k unless the k c-factors are dependent or the k Kronecker
  products a_t (x) b_t are dependent, and likewise for a and b, so a rewrite
  with k-1 products needs that in every slot ("R" candidates; the first
  version of the filter used factor dependencies alone and missed the
  Kronecker case, which is what makes a split pair reducible -- caught by a
  control and fixed the same evening, with no change to the five classes'
  counts up to k = 8); by Kruskal's theorem a k-term decomposition of a
  scheme without repeated factors is unique when two slots are independent,
  so a different k-product rewrite needs dependent factors in two slots ("A"
  candidates).  Two deciders: proj/kres_solve.py, SAT on the residual
  restricted to its support (rank is invariant under that restriction), in
  process through python-sat or one cadical per instance -- 0.1 s per
  refutation at k = 6, 1 s at k = 7, 20 s at k = 8, so hopeless at k = 8;
  and proj/kres_exact.py, exact by slice spaces: tensor rank is at least
  each flattening rank, and rank(R) equals the flattening rank m in a
  direction iff that direction's slice space (2^m - 1 elements) is spanned
  by its rank-one matrices, each rank-one basis being a decomposition.
  Every k <= 7 reduction candidate and all but 108 of km47's 455,573 at k =
  8 have a flattening rank k - 1, so the reduce question is exact in
  microseconds; every two-slot candidate has an independent slot, so the
  alternatives are exactly the other rank-one bases of that slice space.
  Validated against the SAT decider (496 k = 6 refutations; 1267 k <= 5
  uniqueness verdicts; the 430 alternative schemes of 100 trivial-scheme
  triples identical) and on a positive control (a 47 with one product split
  in two is found at k = 2 and reduced back to the identical 47).  Both
  rebuild and Brent-check the full scheme; the alternatives are class-sorted.
  Candidates per class, k = 5 / 6 / 7 / 8, all three flattening ranks below
  k: km47 4 / 496 / 20,052 / 455,573; at47 21 / 1,320 / 38,997 / 732,728;
  ref47 0 / 288 / 14,802 / 370,679; proj47_5 15 / 1,020 / 31,607 / 613,598;
  projkm47_7 6 / 620 / 23,523 / 515,272.  Two dependent slots, k = 4 / 5 / 6
  / 7: km47 19 / 1,248 / 36,833 / 667,486; at47 39 / 2,094 / 53,573 /
  873,744; ref47 12 / 972 / 31,632 / 606,696; proj47_5 27 / 1,572 / 42,581 /
  725,068; projkm47_7 20 / 1,323 / 39,027 / 704,431 (a minute per class to
  k = 8 on 12 threads; proj/logs/kres_exact_sweep_2026-11-09.txt; regenerate
  with kres).  The exact sweep (proj/kres_exact_sweep.zsh, 21:48-21:58,
  12-way): NEGATIVE everywhere.  Reduce: every candidate with a flattening
  rank k - 1 is refuted, 476,017 / 772,928 / 385,661 / 646,132 / 539,283,
  leaving 108 / 138 / 108 / 108 / 138 k = 8 subsets with all flattening
  ranks at most 6 for the SAT decider; so no rank-46 scheme shares 39 or
  more products with any of the five representatives, up to those
  leftovers.  Alternatives: every one of the 3,788,397 two-slot candidates
  has a unique k-term decomposition (705,586 / 929,450 / 639,312 / 769,248 /
  744,801 verdicts), so no other rank-47 scheme shares 40 or more products
  with a known one unless the differing products are dependent in all three
  slots; those 132,771 subsets (k <= 7) go to the SAT decider (k <= 6 fully,
  3,744; k = 7 after a timing sample).  The verdicts are class invariants
  (an isotropy carries products to products and preserves every dependency
  and every decomposition), so one representative per class covers all 193
  schemes we hold: the five known 47s are locally rigid out to seven or
  eight products.  proj/kres_leftovers.zsh (22:00-22:28, log
  proj/logs/kres_leftovers_2026-11-09.txt): the SAT decider refutes all 600
  k = 8 reduce leftovers (2 M conflicts allowed, none needed) and all 3,790
  all-three-dependent subsets with k <= 6 in alt mode (no alternative), so
  the k <= 8 reduce and k <= 6 alt pictures are complete; a sample of 120
  of the 20,052 k = 7 all-dependent subsets in alt mode takes 0.9 s each
  with 22 timeouts at 500 k conflicts, so the 132,771 of them are an
  overnight SAT job.  k = 9 reduce for km47 by the Python decider: 6,993,698
  candidates, 6,988,525 refuted, 5,173 with all flattening ranks at most 7
  left for SAT (16 min on 12 workers).  The decider is now also inside the
  Rust enumerator (`kres --decide`: coordinates with tracking, u128 slice
  matrices, Gray-code enumeration of the slice space, the rank-one span
  test for reduce and the "more than k rank-one elements" test for alt;
  only RED, ALT and undecided lines are written), a few microseconds per
  candidate; it reproduces the Python verdicts exactly on both controls, on
  km47 to k = 7 (every count) and at k = 8 (455,465 refuted, 108 undecided),
  so k = 10 and 11 need no candidate files and take 15 min and an hour per
  class.  proj/kres_overnight.zsh (2026-11-09 night): k = 8..10 for the five
  classes, SAT on the k = 7 all-dependent subsets, rebuild and class-sort of
  anything found, then k = 11 until 06:30.
  2026-11-10 morning, the overnight's outcome (proj/logs/kres_overnight_2026-11-09.txt):
  phase A (k = 8..10, five classes, 22:52-01:32) found NOTHING -- zero
  reducible and zero alternative among the exactly decided candidates --
  and left 166,464 / 293,451 / 140,916 / 261,135 / 217,354 reduce lines
  open (all three flattening ranks at most k - 2; k = 10 mostly, dims
  (8,8,8) and (8,8,7)); phase B's SAT took 4.7 h for km47's 20,052 k = 7
  all-dependent subsets (16,927 unique, 3,125 timeouts at 500 k conflicts,
  no alternative) and its ten-times-budget retry was a 40-hour job, stopped
  at 07:05 with the other four classes untouched.  The open cases are now
  exact too.  The deficient case (kres.rs doc comment): a decomposition of
  R with d terms is the same thing as a space W containing the slice space
  S (dim m) with dim W <= d that is spanned by its rank-one elements (a
  rank-one basis of W gives the terms; the Kronecker matrices of any
  decomposition span such a W; restricting to the factor spans loses
  nothing), so with delta = target - m the question is whether some
  S + <N_1, ..., N_delta> with rank-one N_i is spanned by rank-one
  elements.  For delta = 1 the N are confined: W is spanned only if some
  N + s with 0 != s in S is rank-one too, so s = N + (N + s) has rank at
  most 2, and s must lie outside the span S' of the rank-one elements of S
  to add anything, so s is a rank-two element of S outside S' and N is one
  of its six two-term rank-one splits (the first version also tried the
  2^nr + 2^nc - 4 neighbours of every rank-one element of S, which are
  redundant: 40x slower, identical verdicts on 455,573 subsets); the exact
  test is S' + span{s in S : N + s rank-one} = S.  For delta >= 2 the
  first N runs over every rank-one
  matrix outside S and the rest recurse.  Alternatives in the deficient
  case: a W other than the original space U, or U with more than k
  rank-one elements.  Every YES carries the new products and is verified
  against the tensor of the dropped ones; `kres --lines FILE` decides the
  R / A lines of a candidate file, `--subset` one subset verbosely,
  proj/kres_apply.py splices the products in and Brent-checks the scheme,
  proj/kres_ctrl.py plants controls.  Controls (proj/kres_deep_controls.zsh,
  log proj/logs/kres_deep_controls_2026-11-10.txt): the 600 SAT-refuted
  k = 8 leftovers are refuted; the 3,790 SAT-unique k <= 6 all-dependent
  subsets are unique; a (7,7,7) k = 8 subset with two products split into
  three (same sum, no repeated Kronecker product: (a+a')bc, a'(b+b')c,
  a'b'(c+c')) is reduced from 9 to 8 products through the delta = 1 path
  and a (6,6,6) one of rank 8 through the delta = 2 path, both rebuilt to
  km47 itself; in the split scheme every all-dependent k = 7 subset
  containing a flippable pair (the split products share factors, and the
  third split product happens to share its c-factor with product 29) shows
  an alternative (28,764 ALT; 148,967 reductions where all three split
  products are present; 30 open at delta >= 2) and every one without such
  a pair is unique (20,063); the 16 distinct alternative schemes all
  Brent-check.  RESULTS (proj/kres_deep_lines.zsh, 07:29-07:38, log
  proj/logs/kres_deep_lines_2026-11-10.txt): every open reduce line of the
  five classes is REFUTED -- k = 9: 5,173 / 9,045 / 4,602 / 7,725 / 6,955;
  k = 10: 161,183 / 284,268 / 136,206 / 253,302 / 210,261 (80-150 s per
  class).  So NO RANK-46 SCHEME SHARES 37 OR MORE PRODUCTS with any of the
  193 rank-47 schemes we hold (k <= 10 exact, all five classes).  The k = 7
  all-dependent alternatives question is closed exactly in 2 s where SAT
  needed 4.7 h for one class: all 128,981 subsets (20,052 / 38,997 /
  14,802 / 31,607 / 23,523) are unique, km47's 3,125 SAT timeouts included,
  so NO OTHER RANK-47 SCHEME SHARES 40 OR MORE PRODUCTS with a known one.
  Side fact from the controls: no rank-47 scheme file in the repo (the five
  representatives, found47_km56, the walk parents' 47s, the two 166 points)
  has two products sharing a factor, so Kruskal's two-independent-slot
  criterion is complete for them and no Kauers-Moosbauer flip leaves a 47
  (the flip engine only ever moves through rank 48).  Running from 08:42
  (proj/kres_deep_enum.zsh, scratchpad kres/deep/p3.log; a first launch at
  07:40 was stopped by mistake -- its grep|sed log pipeline was
  block-buffered and read as a stall; kres now logs straight to a file):
  the alternatives question for the all-dependent subsets at k = 8..10
  (delta = 1 for dims (k-1,k-1,k-1)) by re-enumeration, then k = 11 reduce
  + alt, five classes; the k = 8 alt pass over km47's 455,573 all-dependent
  subsets takes 0.7 s, so the sweep should run about as long as the
  overnight's phase A plus k = 11.
  2026-11-10 afternoon: the 08:42 sweep finished k = 8..10 for the five
  classes at 12:32 with NOTHING -- zero reducible, zero alternative, every
  reduce candidate refuted with none left open, 3,868,627,690 alternatives
  questions unique (k = 10: 2,284 / 2,114 / 2,058 / 2,980 / 2,437 s per
  class) -- and 1,079,320 alternatives lines left open (166,464 / 293,451
  / 140,916 / 261,135 / 217,354: the all-dependent subsets two or more
  dimensions short in every direction, dims (8,8,8) at k = 10 mostly);
  k = 11 (reduce + alt) started on km47 at 12:32.  The depth-2 decider as
  first written cost 0.4 CPU-seconds per open line (3,000 k = 10 lines:
  360 s on four threads), ten hours on twelve cores: not the delta = 1
  inner loop (making it linear in the rank-two elements with a bucket
  keyed by split component gained 10%) but the outer loop over every
  rank-one matrix of the slice space (255 x 255 of them at 8 x 8), each
  with a 512-element classification.  Case analysis of W = S + <N1, N2>
  spanned by its rank-one elements, Q its rank-one elements outside S
  spread over the three cosets of S: either two of them share a coset and
  sum to an element t of S outside S' -- t has rank two and N1 may be
  taken among its six splits -- or every same-coset pair sums into S', so
  W = S' + <q1, q2, q3> forces S' to be a hyperplane of S, all three
  cosets hit and t = q1 + q2 + q3 in S \ S' of rank 2 or 3; rank 2 is
  covered by the splits (S + <split> is then already spanned), rank 3
  makes q1 a term of one of the 28 three-term rank-one decompositions of
  t.  So N1 ranges over the splits of the rank-two elements outside S'
  plus, when S' is a hyperplane, the terms of the three-term
  decompositions of the rank-three elements outside S'; the spaces
  S + <N1> already spanned are visited first (the stronger verdict).
  0.2 ms per line, 1,000-2,000x.  Checks: the five controls and the
  455,573-line k = 8 enumeration reproduce the original binary's verdict
  files line for line; the 25,776 open km47 lines containing products 0
  and 1, moved into the split scheme with the third split product
  appended, are planted reductions two dimensions short -- 25,725
  REDUCIBLE and 51 open as three short, none refuted, the exhaustive
  binary identical on a 5,155-line sample; the 30 delta = 2 lines of the
  planted-flip control are all positive (28 RED + 2 ALT against the
  exhaustive binary's 8 + 22: which verdict surfaces first depends on the
  candidate order and the rank-one basis; every one Brent-checks); and a
  randomized unit test (cargo test --release --bin kres) compares the
  depth-1 and depth-2 searches with brute force on 2,120 random spaces in
  six shapes (4x4 to 6x3, dim 2..5): identical, with 311 and 921
  positive instances (proj/kres_depth2_controls.zsh reproduces the
  planted controls).  RESULT (proj/kres_deep_alt2.zsh, 13:28:01-13:28:43):
  1,077,388 of the 1,079,320 open alternatives lines are UNIQUE (7-12 s
  per class); the 1,932 left (406 / 285 / 468 / 282 / 491; dims (7,7,7)
  at k = 10 and (6,6,6) at k = 9: three or more dimensions short) ran at
  depth 3 (the full outer loop over the first extension with the
  restricted depth 2 inside, 13:28:43-13:49:05, 184-334 s per class): ALL
  UNIQUE, none left open.  So the alternatives question is closed at
  k <= 10 exactly like the rank-46 one: every k <= 10 subset of a held 47
  has a residual of rank exactly k with a unique k-term decomposition
  (Kruskal for the subsets with two independent slots, kres for the rest;
  a minimal decomposition lives in the factor supports, so restricting to
  the spans loses nothing), hence NO RANK-47 SCHEME OTHER THAN THE
  ORIGINAL SHARES 37 OR MORE PRODUCTS with any of the 193 rank-47 schemes
  we hold, and no rank-46 scheme does either.  Logs:
  proj/logs/kres_deep_alt2_2026-11-10.txt (with the 1,932 depth-3 lines)
  and proj/logs/kres_deep_enum_2026-11-10.txt (k = 8..10 per class).

- The five rank-47 classes are ONE 48-scheme family (2026-11-10 evening,
  found while preparing a speed-up of kres).  Prior art first: the move
  below is the BLOCK FLIP, and the dependency test of the next bullet the
  2-REDUCIBILITY, of LITA ("Local Improvements to Trilinear Aggregation",
  Khoruzhii, Serafin, Gelss, Pokutta, github.com/khoruzhii/lita, pushed
  2026-10-07, manuscript in preparation; it presents 2-reducibility as a
  strict generalisation of the Kauers-Moosbauer reducibility of
  arXiv:2212.01175 and ships a fast check, src/reduce.h).  We met both
  independently on 2026-11-10 and use their names; nothing here is a new
  move, and neither is the "generalized flip" of Alexandre's bud move
  (tested NULL in October).
  The census: for a direction d take G_d = the span of the 47 Kronecker
  products of the two OTHER slots' factors, and list every rank-one
  element of G_d (proj/kron_census.py, a Gray code over the first factor
  with one small elimination per step; the same census in Rust,
  kres --census, agrees on all five classes and on two planted controls).
  In every class dim G_d = 47 in all three directions (no dependency, so
  no scheme is 2-reducible), and the rank-one elements are the 47 products
  plus exactly ONE extra, in one direction, whose index set is all 47
  products: THE SUM OF ALL 47 KRONECKER PRODUCTS IS RANK ONE (km47 and
  projkm47_7 in direction 1; at47, ref47 and proj47_5 in direction 2).
  The family: with K_t the Kronecker products, z_t the third factors and
  K* = sum_t K_t, every vector beta of the third slot gives
      T = sum_t K_t (x) (z_t + beta)  +  K* (x) beta,
  48 products in general and 47 when beta = 0 (the scheme itself) or
  beta = z_j (product j disappears): 47 neighbours per scheme, none
  sharing a product with it (which is why the k <= 10 statement above
  never saw them).  Scan of all 65,536 beta for km47
  (proj/allsum_betascan.py): exactly those 48 give 47 products.
  Classes of the 48 (proj/allsum_flip.py writes the neighbours,
  scheme_iso.py sorts them, exact): from EACH of the five representatives
  the family splits 24 KM / 12 projkm47_7 / 4 AT / 4 ref47 / 4 proj47_5.
  So NO NEW CLASS, and the five classes we collected over a month are one
  family up to the symmetries of the tensor: one block flip from each
  other.
  Does a second move leave the family?  In the family direction it
  cannot: every member spans the same G_d, whose rank-one elements are
  the 47 K_t and K*, so the 2-reductions of a 48-product member are
  exactly the 48 rank-47 members, and the block flip of a rank-47 member
  is the family again.  For the two other directions, a census of all
  65,536 members of km47's family (proj/allsum_beta_census.py, the 48
  rank-47 members and the 65,488 with 48 products): every member has full
  Kronecker rank and no extra rank-one element.  So no member is
  2-reducible below 47 (no 46 here) and no member has a second block
  flip: the family is closed.
  Logs: proj/logs/kron_census_and_scans_2026-11-10.txt (sections
  kres/census/*).

- 2-reducibility at catalog scale, and RANK RECORDS BY PROJECTION +
  PIVOT SEARCH (2026-11-10 evening).  The test is LITA's (see the bullet
  above for the credit): in direction d write a scheme as
  sum_t K_t (x) f_t, K_t the Kronecker product of the two other slots'
  factors of product t and f_t its slot-d factor; when the K_t are
  dependent, one product per dependency can be dropped after folding its
  f into the others.  Tools: proj/kron_fast.py (the three Kronecker-span
  ranks modulo a prime, from Gram matrices), proj/kron_reduce.py (the
  reduction EXACTLY over Q: dependencies modulo 2^31 - 1, lifted to Q
  from several primes by the Chinese remainder theorem -- a one-prime
  lift fails on the large schemes -- each verified exactly on the
  Kronecker products, then the Brent equations of input and output
  verified exactly by two independent routes, and a corrupted copy of the
  output must be REJECTED), proj/scheme_semantic_check.py (shares no code:
  runs the scheme on random integer matrices in exact rationals, and
  requires a copy with one changed coefficient to fail).
  What we hold (negative).  Every record-rank F_2 store has full
  Kronecker rank in all three directions: 2x4x5 rank 33 (28,202 files),
  3x3x3 rank 23 (201,379), 3x3x4 rank 29 (4,631), 3x3x5 rank 36 (12,005),
  4x4x4 (2,033 files).  Of the 47,320 rank-39 landings of 3x4x4, 8,830
  reduce to 38 (176 of them by a dependency no flip sees); 38 is the
  known record.
  The catalog (dronperminov/FastMatrixMultiplication at 6f8ef61 of
  2026-11-09, 680 shapes, rings Q / Z / ZT): 4,185 scheme files in four
  formats scanned, 21 flagged as 2-reducible, one file not scanned
  (known/mizopl/3x6x8_m108_cr381_cn1412_ZT_reduced.json, an
  addition-reduced program in another layout).  Three flagged files hold
  the catalog's best rank of their shape and ring, and their exact
  reductions are records by themselves: 13x14x14 over Q 1582 -> 1580,
  15x16x16 over Q 2223 -> 2221, 13x14x16 ternary 1806 -> 1805 (the
  catalog's Z and ZT columns; its Q column stays 1796).  The other
  flagged files tie or stay above the catalog's best of their shape
  (11x12x15 and 12x12x14 m1240 -> 1234, 5x12x16 m656 -> 655, ...).
  Projection.  The catalog carries seven square schemes of LITA
  (known/lita: 13x13x13 m1379 and m1420, 14x14x14 m1594 and m1603,
  15x15x15 m1977, 16x16x16 m2237 and m2247).  Deleting one row index of A
  (proj/kron_project.py; products with a zero factor die) gives a scheme
  of the next smaller shape that is 2-reducible, and the catalog's own
  rational entries for those shapes look like exactly that: its 13x14x14
  m1602 and 15x16x16 m2246 files have the rank signatures of the
  projected m1603 and m2247 ([1588, 1602, 1589] and [2230, 2246, 2231]).
  THE DROPPED SET IS A SEARCH SPACE (proj/kron_kill.py).  With N (k x m)
  the dependency space of the K_t, every F + N^T W is a scheme with the
  same K_t, and a zero row is a product gone.  The best W sits at a pivot
  set (k products whose dependencies are independent); exchanging pivot j
  for product t changes only the rows in the support of the normalised
  dependency of j, and the rows that vanish are those sharing t's ratio
  f'_s / N'[j, s], so one step's gain is (size of t's ratio group) -
  (size of the zero group).  Greedy start on the products with most
  companions, then exchange steps with plateau walking.  The gain is not
  "one per dependency" and not even "about two": 29 for 14, 34 for 16,
  113 for 17 dependencies below.
  Results.  Row index 0 of A deleted, pivots found modulo 1048573
  (three trials each, all the same count), then replayed over Q and
  verified exactly twice (kron_reduce.py's two Brent routes with its
  corrupted-copy control, then scheme_semantic_check.py).  The last two
  rows delete a second index from the verified 14x15x15 scheme: inner
  index 0, column 0 of A and row 0 of B (14x14x15), or row 7 of its A,
  the source's row 8 (13x15x15).  The rows marked "row 7/9 deleted" were
  found by the second deletion batch (2026-11-10 23:00, kron_proj_multi.py
  singles) and verified 2026-11-11; they are the records for those shapes:

    shape     LITA source      alive  ranks after the deletion  step                   rank  catalog Q  [S]
    13x14x14  14x14x14 m1594   1594   [1580, 1594, 1580]        d2: 14 dep,  29 gone   1565  1582       1579
    13x14x14  14x14x14 m1594   1594   row 7 deleted             d0: 14 dep,  30 gone   1564  1582       1579
    15x16x16  16x16x16 m2237   2237   [2221, 2237, 2221]        d2: 16 dep,  34 gone   2203  2223       2220
    15x16x16  16x16x16 m2237   2237   row 9 deleted             d0: 16 dep,  35 gone   2202  2223       2220
    14x15x15  15x15x15 m1977   1955   [1938, 1955, 1948]        d0: 17 dep, 113 gone   1842  1848       1848
    14x14x15  15x15x15 m1977   1827   second deletion           d1: 17 dep, 112 gone   1715  1790       1789
    13x15x15  15x15x15 m1977   1797   second deletion           d0: 21 dep,  34 gone   1763  1776       1776

  ([S] = the rank in Sedoglavic's table fmm_sota.json of 2026-11-09 from
  fmm.univ-lille.fr; the per-shape pages read on 2026-11-10 showed older
  values, 1614 / 2262 / 1890 / 1798 / 1797, and the table is ahead of the
  catalog on three shapes.)  All outputs have full Kronecker rank in all
  three directions.  Coefficients are rational and NOT dyadic
  (proj/kron_coeff_stats.py): denominators up to 400 and 200 (13x14x14
  m1565, m1564; primes 2, 5), 720 (15x16x16; primes 2, 3, 5) and 1088 (the
  three 15x15x15 descendants; primes 2, 5, 17).  The 14x15x15 scheme has
  62,867 + 35,592 + 31,539 nonzeros; the projected input's common
  denominators are 5440, 40, 40.  Rescaling every product so that its L
  and R rows are primitive integer vectors leaves one division by a
  constant per entry of C (182 / 195 / 210 / 210 / 240 for the five
  records, two or three distinct constants each).
  All five are non-commutative: proj/scheme_noncomm_check.py runs them on
  matrices whose entries are random 2x2 integer matrices (exact A B), and
  the control with every product's factors swapped fails on every entry.
  They need 2, 5 and 17 (13x14x14: 2, 5; 15x16x16: 2, 3, 5) invertible.
  proj/scheme_modp_check.py reduces a record modulo a prime p and runs it
  over F_p on random matrices: each record is correct at every tested prime
  that divides none of its denominators (3 to 19, 23, 65537, 1048573,
  998244353, 2^31 - 1 and 2^64 - 2^32 + 1) and undefined at the others, and
  a copy with one changed coefficient fails (kron_runs/2026-11-11/
  modp_check.log).
  PLinOpt: proj/json2sms.py writes them as data/<shape>_<rank>_rational_
  {L,R,P}.sms; optimizer -O 1 -s 1 programs; make check passes for all
  five; branch data-rank-records-q, commit 04db52b in the worktree
  matmul/dps48/plinopt_pr/records, opened 2026-11-11 as jgdumas/plinopt#40
  (PR text doc/letters/plinopt_pr_rank_records_2026-11-11.md).  Programs, additions +
  scalings (divisions; proj/slp_div_count.py): 13x14x14 32,015 + 12,945
  (11,422), 13x15x15 16,335 + 3,666 (2,495), 14x14x15 16,825 + 3,890
  (2,680), 14x15x15 17,598 + 3,933 (2,741), 15x16x16 43,925 + 15,699
  (13,636); 11-31% of the divisions are by powers of two.
  One product per dependency would have given 1580, 2221 and 1938: a
  first sweep that screened by that count reported NO candidate for the
  15x15x15 file.  Screen with the pivot search, not with the rank.
  Other deletions, modulo the prime only (proj/kron_proj_multi.py, one
  line per deletion sequence; proj/kron_proj_catalog.py, one line per
  file, for whole directories):
  * 14x14x14 m1603 less row 0: 1574 (below the catalog's 1582, above
    1565).
  * 13x13x13 m1379, all 39 single deletions: 30 reach 1275, 6 reach 1276
    and index 6 of each slot stops at 1340.  The catalog's 12x13x13 is
    1274 (from Sedoglavic's tensor file): one short.  Index 0 verified exactly over Q on 2026-11-11
    (kron_reduced/12x13x13_m1275_Q.*; 15 dependencies, 85 gone; denominator primes 2, 3, 13).  The deleted index
    matters, the slot does not (the same pattern in I, J and K).
  * 15x15x15 m1977, sample single deletions: indices 0 and 14 of every
    slot give 1842, I1 gives 1843, the middle index 7 of each slot only
    1932 (8 dependencies and 14 gone, then 1 and 1).  Forcing the first
    direction is worse: --first 2 gives 1939, --first 1 finds no
    dependency; fold the best direction first.
  * Two deletions from 15x15x15, the pivot search after each
    (kron_proj_multi.py --mode each; the second index is an index of the
    current scheme): I0 then any J or K index gives 14x14x15 at 1715 on
    24 of 30 sequences and below the catalog's 1790 on 28 (worst 1804);
    I0 then I7 gives 13x15x15 at 1763, the other 13 I-sequences 1786 to
    1796.  Deleting both first and reducing once (--mode end) is worse:
    1788 to 1793 for 13x15x15, 1811 for 14x14x15.
  What this is and is not.  The reduction is LITA's 2-reducibility and
  the schemes are LITA's; the catalog's author evidently projects them
  already (the signatures above), and the catalog's records 1582 and
  2223 for these shapes are themselves still 2-reducible by 2.  What is
  added here is the search over WHICH products to drop.  We have not compared with what LITA's own reduction
  (src/reduce.h) drops, and LITA's repository holds 14x14x14 r1593 and
  16x16x16 r2236, one below the catalog's copies: not downloaded (needs
  Greg's say), and the same path applied to them is the obvious next
  step.
  Stored: proj/kron_reduced/<shape>_m<rank>_Q.json.gz (the catalog's JSON
  convention) with .deps.json (the exact dependencies), .path.json
  (deletion, direction, pivots), .reduce.log and .semantic.log, for
  13x14x14 m1564 and m1565, 15x16x16 m2202 and m2203, 14x15x15 m1842,
  14x14x15 m1715 and
  13x15x15 m1763 (the last two hold the second stage; the first stage is
  the 14x15x15 file); the direct
  reductions 13x14x14 m1580, 15x16x16 m2221 and 13x14x16 m1805 (ZT) are
  kept beside them.  Logs: proj/logs/kron_proj_records_2026-11-10.txt.
  Open: the same two-deletion chains from LITA's 13x13x13, 14x14x14 and
  16x16x16 squares (running at this commit), pairs, more pivot-search effort at 12x13x13, and the whole catalog
  (391 files with m >= 1000; about 43 single-thread hours for every
  single deletion) once the kres sweep frees the cores.

- kres enumerator rebuilt on the rank-one census, and k = 11
  (2026-11-10 evening; src/bin/kres.rs, the comment block above
  `struct Census` has the proofs).  The census of the bullet above is
  computed once per class.  A direction is USABLE when its 47 Kronecker
  products are independent and the list of rank-one elements of G_d is
  complete; then for every index set I the rank-one elements of the span
  U_I of its Kronecker products are the |I| products themselves plus the
  extras whose index set lies inside I.  All five classes have one extra
  with index set all 47, so for |I| < 47 there is none, and three facts
  replace most of the decider's work: a candidate of full flattening rank
  in a usable direction is UNIQUE without a call; a slice space of
  dimension |I| - 1 inside U_I is spanned by rank-one elements iff it
  holds |I| - 1 of the products; U_I never holds more than |I| rank-one
  elements.  Work units are index prefixes of length min(3, k - 1) handed
  out one at a time (the old unit, the first index, left a single-threaded
  tail).  Unit tests: 4 pass (census against brute force, prefixes cover
  the subsets, the two older ones).
  Regression against the old binary's passes, counts AND every output
  line identical (seconds on 12 threads):

      class        k = 8        k = 9         k = 10          k = 11        lines compared
      km47         1.3 (57.3)   14.3 (320.8)  171.5 (2284.0)  1458.1 (21006.3)   3,708,935 at k = 11
      at47         2.1          20.6          211.2           -             293,451
      ref47        0.9          10.1          124.4           -             140,916
      proj47_5     1.1          12.4          149.2           -             261,135
      projkm47_7   1.2          12.9          150.3           -             217,354

  (old binary in parentheses; 14.4x at k = 11, 44x at k = 8).
  k = 11, 17,417,133,617 subsets per class, both questions:

      class        reduce candidates   refuted       alt unique       with alternatives   alt open     seconds
      km47           696,533,842       all (0 open)  4,009,871,769    0                   3,708,935    1458.1
      at47           836,152,622       all (0 open)  4,288,209,270    0                   5,863,323    1589.3
      ref47          639,452,711       all (0 open)  3,974,642,490    0                   3,107,355    1360.3
      proj47_5       745,935,616       all (0 open)  3,952,191,420    0                   5,318,037    1488.4
      projkm47_7     739,466,849       all (6 open)  4,136,130,372    0                   4,534,865    1598.9

  So NO RANK-46 SCHEME SHARES 36 OR MORE PRODUCTS with a scheme of the
  five classes (exact, k <= 11), and no alternative rank-47 decomposition
  shows up at depth 1; the open lines (candidates two or more short of a
  spanning set) go to the depth-2 pass as at k <= 10.  The depth-2 pass
  (105 to 191 s per class; alternatives to depth 2, reduce lines to
  depth 3) refutes projkm47_7's 6 open reduce lines and leaves
  9,109 / 10,518 / 9,267 / 9,783 / 12,297 alternative lines open (km47 /
  at47 / ref47 / proj47_5 / projkm47_7; slice dimensions mostly 8,8,8),
  none positive.
  Depth 3 on those lines (2026-11-10 23:03 to 2026-11-12 02:48; 1.3 to
  2.5 s per line at 12 threads, 2 to 4 times the k <= 10 rate; km47 in one call,
  the other four in 500-line chunks after at47's single call hit its
  4 h cap and wrote nothing):

      class        lines open at depth 2   unique at depth 3   open at depth 3
      km47           9,109                   9,109               0
      at47          10,518                  10,518               0
      ref47          9,267                   9,267               0
      proj47_5       9,783                   9,783               0
      projkm47_7    12,291 distinct         12,285               6

  (projkm47_7's 12,297 lines hold each of its six R lines twice, once
  from the R question and once as an A line.)  So NO OTHER RANK-47
  SCHEME SHARES 36 OR MORE PRODUCTS with a scheme of the classes km47,
  at47, ref47 and proj47_5 (exact, k <= 11).  For projkm47_7 the
  statement holds except for six 11-subsets, the same six as its reduce
  lines: their factors span only 7 dimensions in every slot, so their
  slice spaces sit four short of the 11 an alternative needs, beyond
  depth 3.  Their reduce question is settled (refuted above); the
  alternative question needed depth 4:
  0,4,6,13,14,18,23,27,33,36,44 / 1,3,4,12,13,14,18,27,32,38,41 /
  1,3,4,12,13,14,32,34,38,40,41 / 1,4,12,22,26,30,33,34,37,40,43 /
  3,7,9,11,14,18,21,23,27,32,45 / 5,12,30,31,32,34,35,40,41,45,46.
  The class's slot symmetry (perm (2,1,0), transposes 010, in its
  stabilizer; proj/kres_line_orbits.py) fixes the second and third and
  swaps the first with the fifth and the fourth with the sixth, and a
  verdict is constant on an orbit: four lines up to symmetry.
  Depth 4 on the four (2026-11-12 10:10 to 14:15): ALL UNIQUE, so all
  six are.  So NO OTHER RANK-47 SCHEME SHARES 36 OR MORE PRODUCTS with a
  scheme of any of the five classes (exact, k <= 11), the same range as
  the rank-46 statement: k = 11 is complete for both questions.  At
  delta >= 3 the decider extends the slice space by every rank-one
  element outside it, 16,129 first-level extensions here, and runs the
  depth-3 search on each.  kres --shard i/n keeps the extensions whose
  loop index is i mod n, so n runs partition the search: a line is
  unique iff every shard says unique.  96 shards per line, one core
  each, 12 workers.  All 384 jobs exited 0 with "1 unique", every shard
  exhausted its extensions, and the extension counts add up to 16,129
  per line.  Single-core hours per line, in the list's order: 6.5 /
  8.5 / 8.5 / 31.0, 54.4 in all.  Controls: planted alternatives
  (proj/kres_plant_flip.py: k products with factor spans 7,7,7, two
  sharing a c-factor, the alternative checked on the tensor) found and
  verified at delta 3 (k = 10) and delta 4 (k = 11), three seeds each;
  the k = 11 ones through the sharded job script report ALTERNATIVES,
  verified, in the shards holding them (seed 3's extension 128 in shard
  32 of 96) and unique in the 12 shards of seed 1 holding none; 24 km47
  depth-3 lines stay unique in three shards whose times add up to about
  the unsharded run's; cargo test 4/4.
  Drivers as run: proj/kres_census_k11.zsh (the sweep with its
  regressions), proj/kres_census_k11_alt2.zsh (the depth-2 pass),
  proj/kres_census_k11_chain.zsh, proj/kres_census_k11_alt3.zsh,
  kres_census_k11_alt3c.zsh and kres_census_k11_alt3d.zsh (depth 3: one
  call per class, then the chunked run and its resume after the full
  disk of 2026-11-11 08:17), proj/kres_census_k11_alt4.zsh with
  kres_census_k11_alt4_job.zsh (depth 4); logs
  proj/logs/kres_census_k11_2026-11-10.txt,
  proj/logs/kres_census_k11_alt3_2026-11-12.txt and
  proj/logs/kres_census_k11_alt4_2026-11-12.txt.

- Walks at rank 47 from the fifth class (2026-11-08 evening, follow-up 3 of
  the "keep the CPUs busy" queue): flip --walk from its four schemes
  (d180 r47-00007/13/14, d180b r47-00012), excursions up to 2 above 47
  (hard 5), kick 20, seed 11, 180 min, 12 threads
  (proj/logs/walk47_fifth_seed11.log): 239,288,720 landings at 47 and
  only 4 new distinct schemes, all four exactly in the fifth class
  (proj/scheme_iso.py against r47-00007) and all four flip-isolated
  (proj/found47_km56/walk5b).  The class is a closed basin at that
  excursion depth: every landing is one of eight schemes.  The second run,
  excursions up to 3 (hard 6), seed 23, 180 min (proj/logs/walk47_fifth_seed23_x3.log):
  165,047,448 landings, again 4 new distinct schemes, all four exactly in
  the fifth class and distinct from the first run's four
  (proj/found47_km56/walk5c).  Closed at depth 3 as well.  A third run at
  depth 2 with seed 7 (lane B's own, 22:53-01:53, proj/logs/walk47_fifth_seed7.log):
  241,934,175 landings, 4 new distinct schemes, two of them files of the
  earlier runs, all in the fifth class (proj/logs/iso_walk5_seed7.log,
  proj/found47_km56/walk5_seed7).  The broad run from every rank-47 scheme
  we hold (66 files, all five classes) with excursions up to 4 (hard 8),
  seed 31, 180 min (proj/logs/walk47_all_x4_seed31.log): 122,774,727
  landings, 43 new distinct schemes (3 of them files we held), exact classes
  (proj/logs/iso_walk47_all_x4_seed31.log): AlphaTensor's 11, Kauers-Moosbauer's
  13, the projection-descent class 14, the fifth class 4, AlphaEvolve's 1
  (the first scheme of that class any search of ours produced, a neighbour
  of the published one).  No sixth class; the walks move inside classes,
  never between them.  Files in proj/found47_walks/x4_seed31.  The same
  from 62 files with excursions up to 3 (hard 6), seed 29, 180 min
  (proj/logs/walk47_all_x3_seed29.log): 183,496,168 landings, 48 new
  distinct schemes (3 already held), exact classes
  (proj/logs/iso_walk47_all_x3_seed29.log) AlphaTensor's 11,
  Kauers-Moosbauer's 17, the projection-descent class 14, the fifth class 5,
  AlphaEvolve's 1; again no sixth class (proj/found47_walks/x3_seed29).  The
  last run, excursions up to 5 (hard 10), seed 37, from all 110 files held
  including the walk finds, 180 min (proj/logs/walk47_all_x5_seed37.log):
  185,332,690 landings, 33 new distinct schemes (3 already held), exact
  classes (proj/logs/iso_walk47_all_x5_seed37.log) AlphaTensor's 11,
  Kauers-Moosbauer's 10, the projection-descent class 10, the fifth class 2,
  AlphaEvolve's 0; no sixth class (proj/found47_walks/x5_seed37).

  Verdict of the night (2026-11-08 16:20 to 2026-11-09 07:55, cores at full
  load throughout): the third parent bottoms at 51; the AlphaEvolve output
  side resists 22,000 heuristic runs and the exact local search to depth 6;
  six walk runs at rank 47 (three from the fifth class, three from every
  class, excursions 2 to 5, 1.1 G landings) produce 136 new rank-47 schemes
  and not one outside the five known classes.  We now hold 193 distinct
  rank-47 schemes over F2 in five classes, every one flip-isolated where
  checked; the flip graph at rank 47 with short excursions is a union of
  closed basins, one per class, and new classes have come only from new
  parents (AlphaTensor's and Kauers-Moosbauer's <4,4,5>).
  Beside it, follow-up 2: the AlphaEvolve class's output side
  (matmul/x47 seeds/ref47_P transposed, 34 targets, BP 49, floor 41) under
  20,000 plain BP runs (49: 19,369, 50: 631), 2,000 pilot-lookahead runs
  (all 49), and lns at depths 3, 4, 5 (caps 30, 60, 120 min; 3,995 distinct
  BP helper sets, goal 48 = 14 helpers) and depth 6 (cap 3 h; 15,978,924
  neighbourhoods of 8 kept helpers): no program below 49 within any cap
  (proj/logs/aeside_lns_d{3,4,5,6}.log).  The ladder is exhausted; the side's
  cost stays between 41 and 49.

Verdict: projection is a good seed generator exactly where the funnel
is deep.  At the small formats it changes which records are found,
not whether; at 4x4 it turns a 5-minute lottery into a sure landing
at the record level, and it is the only one of the three moves here
that pays.  Logs proj/logs/m3_*.log (per-minute reports, final
counters), driver proj/run_move3.sh.
