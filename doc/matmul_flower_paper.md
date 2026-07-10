# The Flower: Visualizing the Solved-Move Landscape of the Rank-48 4×4 Scheme, and the Search Heuristics It Yields

*Greg Sidebottom*

*Research note — logic repo
(https://github.com/gsidebottom/logic), matmul track, 2026-07-09.
Companion to "Rigidity of the Rank-48 4×4 Matrix-Multiplication Scheme
under Solved Flip Moves" (`doc/matmul_rigid48_paper.md`), which proves
the theorem this note visualizes, and to the 3×3 additive-complexity
paper (`doc/matmul_adds_paper.md`). Interactive version of Figure 1:
https://claude.ai/code/artifact/e2167bb4-fb0d-4295-a0f9-b4554142e39d.
Every number below has a mechanical check (§6).*

## Abstract

The companion paper proves that the rational rank-48 scheme for 4×4
matrix multiplication — the only rank-48 scheme usable over the real
numbers — is *rigid*: the graph of states reachable by one split and
solved flips is finite (7,408 states) and contains no reduction except
the trivial return to the seed. This note treats that certified graph
as **data**. We export it with per-state search metrics, visualize it,
and read off its anatomy, which turns out to be strikingly simple: a
**flower** — a single hub (the seed), 6,488 pendant leaves that admit
no move except undoing themselves, and a thin 920-state *fringe* where
all nontrivial structure lives and where every local search signal
saturates almost immediately.

From the picture we derive six concrete search heuristics, and they
pay off at once: a gradient signal (**nearmiss**, the number of
solvable one-move coincidence targets) that is provably capped at 2
inside the certified component **deepens to 7 and then 14** one split
level further out and, under five levels of beam guidance, reaches a
mean of 85 — 38× a matched-rank random control, certifying the
gradient as heritable structure rather than rank inflation; a 19×
budget-focusing rule; and a cost-recalibration discipline that caught
a uniform
two-split enumeration mispriced by two orders of magnitude (killed at
3% after 18 CPU-hours; its true cost ≈ 500 CPU-hours) and replaced it
with a guided program that covers the region all metrics favor at a
fraction of the price. Whether the deepening gradient ever converts
into an actual rank reduction — a new rank-48 scheme, or the
characteristic-0 rank-47 that would be a record — is the open question
the running campaigns address.

## 1. The graph

All terms from the companion paper; briefly: the **seed** is the
Dumas–Pernet–Sedoglavic rational ⟨4×4×4:48⟩ decomposition (48
rank-one summands a⊗b⊗c over ℤ[½]); a **split** replaces a summand by
two (rank +1, and over ℚ can target *any* partner's factor); a
**solved flip** is a flip whose scalar λ is chosen by solving
`f_i + λ·f_j = μ·f_m` — the only way exact coincidences occur over the
rationals; a **reduction** merges two summands proportional in two
slots (rank −1).

`flip48 --graph` exports the full 1-split component: **7,409 nodes**
(the seed plus 7,408 rank-49 states — independently matching the count
pinned in the Lean theorem) and **16,000 edges** (6,768 splits, 2,328
solved flips, 6,904 reductions), with four metrics per state:

- **shared** — number of factor pairs equal in some slot (flip
  eligibility);
- **coinc** — number of solved flips available;
- **nearmiss** — number of *distinct third summands* reachable by a
  ply-1 coincidence: how many partners this state could become
  aligned with in one move. A reduction needs alignment with the
  *same* partner in *two* slots, so nearmiss counts the doors that a
  second aligned slot would turn into exits;
- **copl** — coplanar factor triples in the a-slot (rank-2 triples):
  the raw material from which solvable moves are made.

## 2. Anatomy: the flower

![Figure 1: the solved-move component. Hub = seed; annulus = 6,488
pendant leaves (aggregated); scattered structure = the 920-state
flip-active fringe, colored by nearmiss, teal-ringed where copl =
109.](fig_flower.pdf)

| measurement | value |
|---|---|
| states / edges | 7,409 / 16,000 |
| reductions → seed | **6,904 of 6,904** |
| degree-2 pendant leaves (split in, reduce back, nothing else) | 6,488 (88%) |
| flip-active fringe | 920 states, 1,468 flip edges |
| nearmiss distribution | 0: 6,568 · 1: 516 · 2: 324 — **maximum 2** |
| coinc distribution | 0: 6,568 · 2: 516 · 4: 324 |
| copl distribution | 63: 2,128 · 64: 4,896 · **109: 384** |
| max coefficient anywhere | 6 (magnitudes never grow) |

Three readings:

1. **The rigidity theorem, as one number.** Every one of the 6,904
   reduction edges points at the seed. The certified statement "no
   reduction except the trivial return" is *visible*.
2. **The component is almost entirely inert.** 88% of states are
   petals — one move in, one move out, no interaction with anything.
   Uniform search effort is 88% wasted by construction.
3. **The fringe is where structure lives, and its signals saturate.**
   Only 920 states have any solved flip at all; no state has more
   than 2 nearmiss targets or 4 available moves; and one
   distinguished band — 384 states with 109 coplanar triples against
   the 63–64 baseline — concentrates the geometric richness. Inside
   the certified component there is, quite literally, no gradient to
   climb: the landscape is flat at height 2.

## 3. The heuristics

**H1 — Spend search where the structure is (19× focusing).** Second
splits from pendant leaves recreate the situation the certificate
already closed. Restricting second splits to the 920-state fringe
(and ordering by nearmiss, then the copl-109 band) concentrates the
budget on ~12% of parents with, empirically, all of the signal.

**H2 — Never walk randomly; only solved moves.** (Restated from the
companion paper as an operating rule.) Ten million random-λ moves
produced zero coincidences; exact events over ℚ are measure-zero.
Every productive move is the solution of a small linear system —
search over ℚ is *constructive*, not stochastic.

**H3 — nearmiss is the gradient.** It measures exactly the
precondition of the goal event (a two-slot alignment with a single
partner). Its ceiling inside the certified component is 2; the
question "is the landscape flat everywhere, or only here?" is decided
by measuring it at depth. Measured: **depth-1 max 2 → sampled depth-2
max 7 → guided beam level-1 max 14 (mean 11.1 over a 1,500-state
beam)**. The gradient is real, and it steepens under guidance — the
strongest empirical argument yet that the rigidity boundary is a
property of the *radius*, not of the whole landscape.

*H3, tested against the null.* A climbing nearmiss curve has a cheap
alternative explanation: a depth-k state has 48+k summands, so the
count of possible alignments could inflate mechanically with rank,
and a beam would then be "climbing" a staircase that rises under
everyone's feet. The control (`--nmrand`): at each depth, 5,000
*unguided* random split-walks from the seed, nearmiss of each raw
endpoint — same split distribution as the beam, no selection, no
inheritance. Matched at equal rank:

| rank | beam mean | beam max | random mean | random p99 | random max (5,000) | top-1,500 of 5,000 |
|---|---|---|---|---|---|---|
| 50 | 5.1 | 9 | 0.21 | 5 | 9 | 0.7 |
| 51 | 14.3 | 29 | 0.51 | 6 | 12 | 1.7 |
| 52 | 27.9 | 50 | 0.92 | 7 | 17 | 3.0 |
| 53 | 51.1 | 76 | 1.55 | 10 | 27 | 4.6 |
| 54 | **85.3** | 122 | 2.22 | 12 | **20** | 6.0 |

Rank inflation exists but is tiny (unguided mean reaches only 10.5 by
rank 61, the campaign's terminal depth — the beam passed that at
level 2). At rank 54 the beam's *mean* is 38× the unguided mean, 7×
the unguided 99th percentile, and 4× the unguided *maximum over 5,000
draws*; one-shot selection without guidance (best 1,500 of 5,000)
achieves 6.0, i.e. 7% of the beam mean. A typical beam state
outscores the best unguided state of equal rank — no one-shot
selection from the unguided distribution produces that. The only
mechanism left is inheritance: high-nearmiss parents beget
higher-nearmiss children. And the beam/null ratio itself climbs
(24× → 28× → 30× → 33× → 38× across levels 1–5): guidance compounds.
**The gradient is heritable structure, not a rank artifact.**

**H4 — The copl band is a prior.** Coplanarity is the raw material of
solvable moves; the 384-state copl-109 band is the natural first
target for any deeper enumeration, and band membership is computable
before committing any search budget to a parent.

**H5 — Measure closure inflation before exhausting.** The 1-split
closures average 2.3 states; a uniform 2-split enumeration priced at
that figure looked like a ~10-CPU-hour job. Direct measurement showed
level-2 closures average **~580 states (250×)** — repricing the
uniform sweep at ~500 CPU-hours. It was killed at 3% (18 CPU-hours
spent) and replaced with the guided program below. The rule: before
exhausting level k+1, measure its branching on a sample; the
extrapolation from level k is not a bound, it is a guess.

**H6 — A certificate needs an audit trail, not a counter.** The first
fringe-exhaustive campaign hit its state budget at "~644 of 840
parents done" — and could not say *which* 644. Its parents were
processed by a work-stealing parallel loop, so the completed set was
a scattered, nondeterministic subset, not a prefix (a 2-parent test
run completed indices 76 and 2,775); a planned prefix-skip resume
would have silently left coverage holes in the certificate, and was
retracted before use. The rule: any enumeration whose value is the
claim "*all* of X was covered" must log the *identities* of completed
work (stable across runs), not a count — completeness of coverage is
otherwise unrecoverable from the survivor. The engine now appends
each finished parent index to `fringe_done.txt`, and `--resume` skips
exactly the logged set; campaign 1's 4.02 billion states stand as
evidence, campaign 2 is the certificate run.

## 4. The running program, and the open question

Two campaigns implement the heuristics (both with progress tickers,
global state budgets, and inline exact verification of any find):

- **Fringe-exhaustive** (`--pursue5 0 --fringe-only`): *all* 7,056
  second splits of each of the 840 gradient-positive parents, every
  root closed under solved flips with reduction continuations. Zero
  findings here extends the rigidity certificate to "no reduction
  reachable through the fringe at 2-split radius." Campaign 1 closed
  at its 4×10⁹ budget: **4.02 billion states, ~644/840 parents
  (scattered — see H6), zero reductions**, depth-2 nearmiss ceiling
  14. Campaign 2 (completion-logged, exactly resumable, budget
  7×10⁹) is re-running all 840 for the certificate; at writing,
  189/840 with the same zero-reduction, ceiling-14 profile.
- **Gradient chase** (`--pursue6`): best-first beam on nearmiss
  across split depths (beam 1,500, 60 sampled splits per frontier
  state, closure cap 150). Through level 5 (rank 54): nearmiss max
  122, beam mean 85.3, with the per-level mean *accelerating* (+9.2,
  +13.6, +23.2, +34.2) while the unguided baseline crawls (+0.3,
  +0.4, +0.6, +0.7) — and the H3 control certifies the climb is not
  rank inflation. Yet through 450 million states, **zero
  conversions**: over a hundred one-slot alignments available per
  frontier state and not one same-partner second-slot event has ever
  fired. The chase asks the one question that matters: **does
  nearmiss keep climbing until a double-coincidence actually fires,
  or is there an obstruction — a radius-independent invariant
  separating alignment from reduction?** A conversion produces a
  genuinely new rank-48 scheme (fresh material for the
  operation-count program of the companion papers) or a
  characteristic-0 rank-47 — a record. A plateau — or a curve that
  climbs forever without converting — maps the next rigidity
  boundary.

## 5. Why visualize at all

The honest answer: every quantitative decision in §3 was *available*
in raw logs, and none of it was *seen* until the graph was drawn. The
flower shape — hub, petals, thin fringe — made three facts
simultaneously obvious that tables had kept separate: reductions all
point home; almost everything is inert; the interesting minority is
small enough to exhaust. One picture converted a mispriced brute-force
plan into a guided program and surfaced the gradient question that is
now the campaign's spine. For search spaces born from exact algebra,
where every state is expensive to think about individually, a faithful
picture of the *whole* is the cheapest instrument there is.

## 6. Reproduction

```bash
cargo build --release --bin flip48
./target/release/flip48 --graph matmul/dps48/graph48.json --cap 256   # 17 s
# anatomy numbers: any JSON tool over graph48.json (see §2 table)
./target/release/flip48 --pursue5 0 --fringe-only --threads 8 \
    --budget 7000000000            # fringe-exhaustive campaign
# completed parents log to found48q/fringe_done.txt; add --resume
# after any interruption to skip exactly the logged set (H6)
./target/release/flip48 --pursue6 --beam 1500 --samples 60 --depth 8 \
    --threads 4                    # gradient chase
./target/release/flip48 --nmrand 13 --n 5000 --threads 4  # H3 null
```

The interactive Figure 1 (hover any fringe state for its metrics) is
published at the artifact URL in the front matter; the static figure
is regenerable from `graph48.json` by the script in the repository
history.

## Acknowledgments

This work was carried out in an extended interactive collaboration
with Claude (Anthropic; the Fable 5 and Opus 4.8 models), which
implemented the engines, the export and visualization, and much of
this text under the author's direction and review. Every number is
mechanically checkable via §6.

## References

- G. Sidebottom. *Rigidity of the Rank-48 4×4 Matrix-Multiplication
  Scheme under Solved Flip Moves — a Machine-Checked Obstruction.*
  Companion paper, this repository (2026).
- G. Sidebottom. *A 55-Addition Rank-23 Scheme for 3×3 Matrix
  Multiplication via Exact Two-Sided Minimization.* This repository
  (2026). Artifacts: DOI 10.5281/zenodo.21240904.
- M. Kauers, J. Moosbauer. *Flip Graphs for Matrix Multiplication.*
  arXiv:2212.01175 (2022).
- J.-G. Dumas, C. Pernet, A. Sedoglavic. *A Non-Commutative Algorithm
  for Multiplying 4×4 Matrices Using 48 Non-Complex Multiplications.*
  arXiv:2506.13242 (2025).
- A. Novikov et al. *AlphaEvolve: a Coding Agent for Scientific and
  Algorithmic Discovery.* arXiv:2506.13131 (2025).
