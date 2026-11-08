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
  tables); the +4 window, 7698 triples including all 646, is being
  refined and settled from the saved tables (2026-11-07 evening, Q6b, all
  four classes, km47 first; km47's 1824 triples done at 20:13: no point
  below 167, the record exact over its +4 window, matmul/x47/README.md).  The climb of the whole-orbit lower bound
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
  what found the class that holds the record.

Verdict: projection is a good seed generator exactly where the funnel
is deep.  At the small formats it changes which records are found,
not whether; at 4x4 it turns a 5-minute lottery into a sure landing
at the record level, and it is the only one of the three moves here
that pays.  Logs proj/logs/m3_*.log (per-minute reports, final
counters), driver proj/run_move3.sh.
