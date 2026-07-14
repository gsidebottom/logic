# Moves on the Space of Bilinear Schemes: a Field Guide to Rank-Hunting Search

*Reproducible methods note — logic repo, matmul track, 2026-07-14.
Companion to the flower, adds, 53-schemes, and zkML papers; all
engines cited live in this repository.*

## 1. The space

Fix a format ⟨m,m,m⟩ and a coefficient field K. A **scheme of rank
r** is a decomposition of the matrix-multiplication tensor into r
rank-one terms,

```
T_m = Σ_{t=1..r}  a_t ⊗ b_t ⊗ c_t ,     a_t, b_t, c_t ∈ K^(m×m)
```

verified by the m⁶ Brent equations. The **space** is the union of
rank strata: at 3×3 the stratum r = 27 contains the naive scheme,
r = 23 the records (17,376+ known classes over ℤ), r = 22 nothing
known; at 4×4 the strata run 64 (naive), 49 (Strassen²), 48
(dyadic records over odd characteristic), 47 (characteristic 2
only). Two schemes are **equivalent** (de Groote) if a sandwich
(P·a·Q⁻¹, Q·b·R⁻¹, R·c̃·P⁻¹), a cyclic slot rotation, or a
per-summand rescaling maps one to the other; searches operate on
gauge-canonical representatives (monic slots over 𝔽_p; primitive
sign-normalized over ℚ).

What is known about the *shape* of this space, from the literature
and from this repository's certificates:

- **It is disconnected at bounded rank.** Kauers–Moosbauer's walks
  from the 3×3 naive scheme land in 584 distinct connected
  components of the rank-≤23 flip graph (64,061 vertices). Our 4×4
  fringe certificate is a completeness proof of confinement: the
  rank-48 seed's component under solved dyadic moves at rank ≤ 50
  is *finite* — 920 states in 16 clusters hanging off the seed as
  a cut vertex, exhaustively enumerated and closed.
- **Altitude connects, but slowly.** Splits (rank+1 excursions)
  merge components: our chase explored eight levels above the 4×4
  seed (1.45B states) without meeting a second rank-48 class —
  connectivity via altitude, if true, is expensive.
- **The field changes the geometry.** Over 𝔽₂ the factor value
  space has 2^(m²) points, so equal factors and coplanar triples
  arise by birthday collision as a walk churns; over a 64-bit
  proof field the value space is effectively infinite, collisions
  never occur, and only *algebraically solved* moves create the
  coincidences that descents spend (measured: 448M flips with random and
  small-dyadic λ from naive over Goldilocks produced zero
  reductions; the same protocol over 𝔽₂ produced ~60 within
  minutes).

## 2. The moves

Notation for the toy examples: e_ij is the matrix unit; the naive
2×2 scheme has eight summands e_ik ⊗ e_kj ⊗ e_ij; Strassen's seven
summands are labeled M1..M7 (M1 = (e11+e22)⊗(e11+e22)⊗(e11+e22),
M2 = (e21+e22)⊗e11⊗(e21−e22), M6 = (e21−e11)⊗(e11+e12)⊗e22, …).

**M-1. Flip** (rank-preserving; the K–M edge). Two summands whose
slot-s factors are *equal* (post-gauge) exchange material in the
other slots: with shared a and transfer λ,

```
u⊗b₁⊗c₁ + u⊗b₂⊗c₂   →   u⊗(b₁+λb₂)⊗c₁ + u⊗b₂⊗(c₂−λc₁)
```

Toy (naive 2×2, summands (1,1,1) and (1,1,2), both with a = e11,
λ = 1): b₁ ← e11+e12 and c₂ ← e12−e11; expanding shows the two
cross terms cancel and the sum is unchanged. Over 𝔽₂, λ = 1 is
the only choice; over ℚ we restrict λ to dyadics (coefficient
control); over 𝔽_p any λ ≠ 0 is legal. Engines: every flip
binary; cost O(m²) per move.

**M-2. Reduction** (rank −1, and the characteristic-2 −2). Two
summands sharing *two* slots merge:
u⊗v⊗c₁ + u⊗v⊗c₂ = u⊗v⊗(c₁+c₂); if c₁+c₂ = 0 both vanish — over
𝔽₂ this fires whenever two summands become fully identical, a
rank −2 event with no analogue over large fields. The ℚ/𝔽_p
variant also merges shared-slot pairs whose third slots are
*proportional*. Reductions are the only rank-lowering moves; every
record descent is a sequence of flips punctuated by them.

**M-3. Split** (rank +1). Rewrite f_i = μf_k + (f_i − μf_k) in one
slot, producing a summand that *shares* that slot with summand k:

```
Strassen toy (μ=1, slot a, against M2):  a(M1) = e11+e22
  →  (e21+e22) ⊗ b(M1) ⊗ c(M1)  +  (e11−e21) ⊗ b(M1) ⊗ c(M1)
```

Splits buy altitude and manufacture shared pairs (the flip fuel);
the flower's 16 clusters are all reached through them. A fresh
split's two parts share *both* other slots, so a reduce-on-sight
walk must be gated (the split/merge livelock we hit building
pursue9: reductions legal only after an intervening flip).

**M-4. Solved flip** (coincidence-targeted; ours). For a shared
pair (i,j) and a third summand m, solve f_i(t) + λ·f_j(t) = μ·f_m(t)
by 2×2 Cramer in the transfer slot t: the flip with *that* λ makes
summand i's t-factor proportional to m's — an alignment created by
algebra, not luck. Toy: T1 = u⊗b₁⊗c₁, T2 = u⊗b₂⊗c₂,
T3 = u′⊗(b₁+b₂)⊗c₃: the pair (T1,T2) shares slot a; solving in
slot b gives λ = 1 (b₁ + 1·b₂ = 1·(b₁+b₂)), and after the flip T1
and T3 share slot b exactly. Over 𝔽₂ every coincidence solution
has λ = 1, so the solved and random flips coincide in *value* and
differ only in *selection*; over 𝔽_p the solved λ is one specific
field element that sampling would never hit — solved flips are the
only reliable coincidence factory (measured, §1). Engines: all
storms' targeted branch; pursue7/10.

**M-5. Closing move** (second-alignment factory; ours). Given an
*already aligned* pair (i,j) — one shared or proportional slot — 
search for a single flip of j against any third summand that makes
a second slot of (i,j) proportional, after which M-2 fires.
This is the pair-focused finisher that turns one-slot alignments
into reductions; over 𝔽_p it needs coplanar triples in the
transfer slot (generic states lack them — the structural reason
naive-descent fails over big fields), over structured scheme
neighborhoods it is routine (every storm quench).

**M-6. Sandwich (symmetry) move** (planned). Apply (P,Q,R) ∈
GL(m,K)³: a gauge teleport. Flips are equivariant, so the flip
graph's components come in isomorphic families (K–M observe
isomorphic components; the sandwich move merges each family into
one search component). Toy: conjugating Strassen by
P = [[1,1],[0,1]] permutes its factor set — same class, different
representative, possibly different local flip options. Cheap and
strictly connectivity-increasing.

**M-7. Closure jump** (planned for 𝔽_p; exists over 𝔽₂ in anf).
Fix two of the three factor tensors; the Brent system becomes m²
independent linear systems in the third — solve exactly. When the
current products are linearly independent the solution is unique
(no move); when dependent, the solution space is positive-
dimensional and the jump teleports across it. Toy: at rank 8 one
split above Strassen, the eight products span a 7-dimensional
space, so fixing α,β leaves a 1-parameter γ-family — the closure
walks it in one step. This is the strongest non-local move we
know that stays field-generic (pure linear algebra).

**M-8. Repair hop** (built: pursue8 --repair). Delete k summands,
beam-rebuild the residual in ≤ k−1 (record event) or k (lateral
hop). Exhaustive over C(r,k) at small k — this is how the local
rigidity certificates were bought (3×3: all 30 census seeds k ≤ 9
rigid over two fields; 4×4: DPS-48 k ≤ 7 rigid over Goldilocks,
73.6M subsets). As a *walk move* (k = 2 lateral) it hops between
flip components at bounded cost.

**M-9. Constructor move** (AlphaTensor's game; built: pursue8).
Forget schemes: hold a residual tensor, subtract arbitrary
rank-one terms until zero. Complete in principle — every scheme is
reachable — but unguided beam search stalls at the Strassen hump
(3×3: terminal count 27; measured), which is precisely the gap a
learned policy filled for DeepMind. Toy: the first constructor
move toward Strassen subtracts M1 from T₂, leaving a residual of
slice-rank 6.

**M-10. Completion jump** (HKS method 2; built: walk.py over 𝔽₂).
Freeze a random subset of a known scheme's coefficient bits,
re-solve the rest with SLS. Non-local, powerful, and the engine of
our 53-scheme discovery and the 715-scheme method-2 basin
measurement; field-restricted to where a solver exists (SAT over
𝔽₂; over 𝔽_p the analogue is M-7's linear closure or Gröbner
methods).

## 3. Search techniques tried (with verdicts)

| technique | engine | verdict (measured) |
|---|---|---|
| random-walk storm portfolios | flip23/flip48/flip23p storm | 81 new ℤ-classes; 63 field-novel patterns; no 22/47 |
| exhaustive closure (BFS + hash) | --native/--lams | exact component maps; F_p seed components trivial |
| depth-2 exhaustive fringe | pursue5 | certificate: 840 parents closed, 0 reductions |
| beam search on nearmiss | pursue6 chase | 8 levels, 1.45B states, gradient 57× null — and 0 conversions |
| mix-and-quench | pursue7 | calibrated bands; ~31M walks over 3 fields; pools, no records |
| constructor beam | pursue8 | Strassen-hump stall at 27 (honest unguided baseline) |
| exhaustive k-repair ladders | pursue8 --repair | rigidity radii: 3×3 k≤9 (×30 seeds ×2 fields), 4×4 k≤7 |
| persistent monotone walk | pursue9 | 𝔽₂ 64→53 then single-trajectory starvation; 𝔽_p sterile |
| frontier pool ladder (K–M Alg. 2) | pursue10 | 𝔽₂ 64→49 in 3 minutes; running |
| SAT completion compounding | walk.py + anf | 53 new schemes in 6 min; method-2 basin ≈ 715 from classics |
| native-ANF SLS | anf | 8/10 HKS challenge-1; ≥5,000× yalsat repair horizon |
| seeding by mobility census | census + SHORTLIST | nm/coinc metrics; hi-band calibration |
| null-controlled methodology | nmrand | beam/null 57×: gradients real, not rank inflation |

Planned next (§2 numbers): M-6 sandwich moves, 𝔽₂ solved-flip
targeting, M-7 closure jumps over 𝔽_p, M-8 as walk move,
Moosbauer–Poole symmetric-subspace walks, commutative flipC, and
learned guidance (the neural track's gmi/gmi_mcgs engines).

## 4. Classical search algorithms on this space

The rank hunt is a single-agent search: **state** = gauge-canonical
scheme; **actions** = the moves of §2; **goal** = any state of rank
below the record (verification is O(m⁶), cheap); the graph has
heavy transpositions (many paths to the same scheme — hash
canonical forms). Two cost models matter: *hop count* (every move
1) and *altitude* (splits cost 1, flips 0, reductions −1 — how far
above the record must a path climb?).

**BFS.** Complete and optimal in hops; memory O(frontier). This is
exactly our `--native` closure and the fringe/flower enumerations —
feasible when the reachable set is 10⁶-ish (the seed's component:
920; the fringe: 9.4B *states* but only depth 2). Use for
certificates, not for hunting: the 𝔽₂ rank-≤47 stratum is beyond
any frontier memory.

**DFS / iterative deepening.** O(depth) memory; our random walks
are memoryless randomized DFS without backtracking; principled
DFS-with-visited appears in cfloor's IDDFS (the adds lower-bound
sweeps) where depth caps make it exact. For rank hunting plain DFS
commits too hard to early moves; ID-DFS re-expands cheaply only
when the branching factor dwarfs depth — true here (branching
10²-10⁴, useful depths 10⁵+) so *not* attractive.

**Uniform-cost search / Dijkstra / SPF.** With unit costs it *is*
BFS. It earns its keep under the altitude cost model: charge
splits 1, flips ε, reductions 0, and UCS over (state) computes the
*minimum-altitude descent* — "how high must any path climb to
leave this basin" — which is exactly the quantity the flower's
cut-vertex anatomy and the chase probe empirically. Frontier
memory again confines it to component-scale questions, where it
would upgrade "we found no crossing at +8" to "no crossing exists
below +9."

**A\*.** UCS plus a heuristic h(state) lower-bounding cost-to-goal.
The obstruction is honest: an *admissible* h would need a
state-dependent lower bound on "distance to a smaller-rank
scheme," and the only rigorous bounds we possess (flattening/slice
ranks, counting floors) bound the *tensor*, not the *path*. Our
practice is therefore the inadmissible cousins: the chase is
**greedy best-first** on nearmiss (h only, no g), null-certified
to carry real signal (57×) yet Goodhart-prone (289-nearmiss states
with zero conversions); weighted-A* interpolations are available
the moment any admissible ingredient appears. A concrete candidate:
h = (current rank − best rank of any scheme sharing ≥ r−k terms,
from the repair ladders) — piecewise-constant, admissible within
radius k, and computable from certificates we already own.

**Minimax and α/β.** No adversary, so minimax proper does not
apply (a MAX-only tree is just DFS). But α/β's *soul* — cut a
branch when a bound proves it cannot beat the incumbent — is
**branch-and-bound**, and we already run it: the adds program's
floors (orbit side-floors + strict-target IDDFS) prune exactly
this way ("this class floors at ≥56, stop"), and the repair
ladders prune subset-trees by projected completion size. The
transferable idea is to give the *rank* hunt the same treatment:
prune walk basins by certified component invariants rather than
walking them dry.

**MCTS / MCGS.** The best fit of the family, with precedent:
AlphaTensor *is* MCTS with a learned prior on M-9's constructor
space. Formulation: node = scheme (graph search with transposition
table — MCGS, since our space is a graph, not a tree); action =
move; rollout = storm/pursue10 walk; reward = −(best rank
reached), or shaped by coincidence density; selection = UCT.
Unguided MCTS at equal budget must be compared honestly against
best-of-K walks (our standing methodology note: apparent MCTS wins
at low budget can invert at matched budget). The repository
already carries MCGS scaffolding from the neural track (gmi,
gmi_mcgs), so the marginal build is the environment adapter, and
the natural first target is the 𝔽₂ 47 ladder, where ground truth
exists and rollouts are cheap (~10⁵ flips/s/core).

**Summary table.**

| algorithm | fits? | as what | status |
|---|---|---|---|
| BFS | yes (bounded sets) | closures, certificates | in use |
| DFS/IDDFS | partially | cfloor sweeps; walks ≈ random DFS | in use |
| UCS/Dijkstra/SPF | yes, altitude cost | min-altitude basin escape | possible |
| A* | blocked on admissible h | greedy best-first (chase) today | partial |
| weighted A* | yes | nearmiss + repair-radius h | planned |
| minimax | no adversary | — | n/a |
| α/β spirit (B&B) | yes | floors/repair pruning | in use |
| MCTS/MCGS | yes | guided constructor/ladder | scaffolding exists |

## 5. One formulation to hold them all

Define the **layered scheme multigraph** G(K, m): vertices are
gauge-canonical schemes stratified by rank; intra-layer edges are
flips (M-1, M-4, M-6, M-7 jumps); downward edges are reductions
(M-2); upward edges are splits (M-3); non-local chords are repair
and completion hops (M-8, M-10). Every technique in §3 is a
traversal policy on G; every algorithm in §4 is a standard policy
with a cost model chosen from {hops, altitude, compute}; every
certificate we publish is an exactly-explored finite subgraph of
G. The record hunt is: *find any vertex in a layer below the
known minimum* — and the disconnection results of §1 say the
interesting question is not which traversal is cleverest but
which *edge set* makes the target layer reachable from where we
stand. That is why the move inventory of §2, not the algorithm
zoo of §4, is this note's center of gravity.

## Acknowledgments

This note was prepared in an extended interactive collaboration
with Claude (Anthropic; Fable 5), which implemented the engines
and drafted the text under the author's direction and review.

## References

1. M. Kauers, J. Moosbauer. *Flip graphs for matrix
   multiplication.* ISSAC 2023; arXiv:2212.01175.
2. J. Moosbauer, M. Poole. *Flip graphs with symmetry and new
   matrix multiplication schemes.* ISSAC 2025; arXiv:2502.04514.
3. Y. Arai, et al. *Adaptive flip graph algorithm for matrix
   multiplication.* 2024.
4. A. Fawzi, et al. *Discovering faster matrix multiplication
   algorithms with reinforcement learning.* Nature, 2022.
5. M. J. H. Heule, M. Kauers, M. Seidl. *Local search for fast
   matrix multiplication.* SAT 2019; arXiv:1903.11391.
6. H. F. de Groote. *On varieties of optimal algorithms for the
   computation of bilinear mappings.* 1978.
7. G. Sidebottom. *The Flower*, *53 New Integer Schemes*, *The
   Additions Ledger*, and *Bilinear Rank and zkML.* Companion
   reports, this repository, 2026.
