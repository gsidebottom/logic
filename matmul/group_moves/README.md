# Subspace re-decomposition moves in the F2 flip engine: equal-budget A/B (2026-11-06)

Question (from Sedoglavic's remark on Tomar's arXiv:2610.11823 and the
projection lemma he used to lower catalog entries): does re-decomposing
the partial sum of a GROUP of terms, exactly, open rank reductions the
flip graph misses?  "Move 1" = src/flip_group.rs:

- G1: k terms with the same factor u in one slot, partial sum
  u (x) M with M = sum b c^T; if rank M < k, rewrite with rank M terms
  (k = 2 is the ordinary merge; k >= 3 is new).
- G2: k >= 3 terms whose factors in one slot lie on a line {p, q, p+q};
  P = p (x) M_p + q (x) M_q is re-decomposed with first factors in
  span{p, q} at cost rank(M_p + N) + rank(M_q + N) + rank(N), N greedy
  from rank-one matrices lowering both ranks (exact rank-one test over
  F2 by the determinant lemma; three choices of the shared element).
  The greedy equals the exact pencil rank on 300 random 4x5 pencils
  (test line_cost_against_exact_pencil_rank; 0 excess).  A k = 3 line
  reduction is one flip + one merge; k >= 4 goes beyond flips.
- `--group-moves 1`: group_reduce tried wherever a merge is tried
  (step 0 of guided_descend, in its steered burst, and as a fallback
  after seek_reduction).  `--group-moves 3` adds `--shuffles N`
  plateau line re-decompositions (cost <= k) per stalled round.
  `--group-moves 0` (default) is the engine before this change.

Protocol: 12 threads, 5 min, seed 7, one run per arm, the same binary
(target/release/flip) for all arms; arms run back to back on an idle
machine.  Logs in logs/, drivers run_arms.sh and run_t5.sh, probe in
probe_chain.sh (src/bin/group_probe.rs).

## Descents

| task | arm | min rank (when) | reductions | trajectories | diffuse flips | distinct landings | group moves fired (g1 / g2 separate / g2 shared / shuffles / terms saved) |
|---|---|---|---|---|---|---|---|
| T1 <4,4,4> from trivial 64 | 0 baseline | 49 (211 s) | 82,127 | 92,239 | 1474 M | 226 at 49 | - |
| | 1 reductions | 56 (15 s) | 49,683 | 54,956 | 900 M | none <= 49 | 1203 / 1626 / 4536 / 0 / 7365 |
| | 3 red.+shuffles | 55 (91 s) | 42,220 | 46,565 | 765 M | none <= 49 | 1058 / 1345 / 3866 / 2.19 M / 6282 |
| T3 <3,3,4> from trivial 36 | 0 | 29 (6.7 s) | 26,690 | 6,379 | 83.5 M | 1560 at 29, 5254 at 30 | - |
| | 1 | 29 (2.1 s) | 18,967 | 4,637 | 60.5 M | 974 at 29, 3823 at 30 | 4109 / 1005 / 2010 / 0 / 7445 |
| | 3 | 29 (7.1 s) | 19,774 | 4,776 | 62.3 M | 1063 at 29, 3960 at 30 | 4385 / 1210 / 1890 / 178 k / 7849 |
| T2 <4,4,4> from Strassen^2 49 | 0 | 49 | 0 | 6,273 | 74.8 M | - | - |
| | 1 | 49 | 0 | 3,225 | 38.4 M | - | 0 / 0 / 0 / 0 / 0 |
| | 3 | 49 | 0 | 3,178 | 38.0 M | - | 0 / 0 / 0 / 108 k / 0 |

T3 per trajectory: distinct 29s 0.245 / 0.210 / 0.223, landings 1.47 /
1.48 / 1.44, reductions 4.18 / 4.09 / 4.14 (arms 0 / 1 / 3): the moves
take over a share of the reductions (in arm 1, 3015 of 18,967 were G2
reductions, which the baseline has no move for) without changing what a
trajectory reaches.  The cost is throughput: 61-72 % of the baseline's
diffusion flips in the descents (51 % on the Strassen^2 start, where
the group scan runs inside every guided round and never fires).
T1's single baseline success (1 trajectory in 92 k reached 49) is a
rare event; the move arms, with 55 k and 47 k trajectories, saw none,
consistent with the throughput loss alone.  No arm on any task reached a
rank the baseline did not.

The T1 baseline printed its final line at 300 s and then hung at exit
until the 390 s grace timeout (exit 124): workers checked the stop flag
only when a diffusion-flip counter hit a multiple of 512, which deep in
guided descent could take minutes.  Fixed after the campaign (checked
every round); results unaffected.

## Fixed-rank walks

| task | arm | landings | new distinct schemes | group moves (g1 / g2sep / g2shared / shuffles / saved) |
|---|---|---|---|---|
| T4 <4,4,4> walk at 47 (3 published seeds, excess 2/5) | 0 | 12,618,618 | 3 | - |
| | 1 | 11,931,275 | 3 | 117 k / 105 k / 441 k / 0 / 666 k |
| | 3 | 6,465,988 | 3 | 66 k / 59 k / 252 k / 28.4 M / 1.63 M |
| T5 <3,3,4> walk at 29 (AlphaTensor's F2 scheme, excess 3/6) | 0 | 3,338,494 | 2570 | - |
| | 1 | 1,437,018 | 2073 | 65 k / 82 k / 178 k / 0 / 325 k |
| | 3 | 1,174,647 | 1956 | 65 k / 83 k / 177 k / 9.09 M / 1.10 M |

T4: the seven schemes found across the arms differ from the nearest
seed by 14 to 47 summands and are new to matmul/x47; no arm found more
than three in five minutes, none a 46.  T5: after the first minute the
baseline adds about 250 new distinct 29s per minute, arm 1 about 160,
arm 3 about 125; per landing the move arms are more diverse (1.4-1.7
new per 1000 landings against 0.8), because a line re-decomposition
lands somewhere a flip path would not, but per second the baseline
wins.  No 28 in any arm.  (A landing below the walk's target rank was
silently discarded by the walk before this campaign; the collector now
verifies and announces it.  Nothing was lost here: the moves' counters
and the worker ranks say no sub-29 or sub-47 state was ever held.)

## Direct probe at visited states (src/bin/group_probe.rs)

States written by the baseline engine (seed 11; <3,3,4> 60 s with
save-at 30, <4,4,4> 45 s with save-at 56), each probed with fresh copies:
`base` = guided_descend without the moves, 3 tries of the engine's own
seek budget (100,000 flips); `group` = one group_reduce, no flips;
`shuf` = 200 plateau shuffles each followed by group_reduce; `both` =
guided_descend with the moves, 3 tries.  Logs probe334.log, probe444.log.

| states | census: same-factor groups k=3/4/5 | lines k=3/4/5/6/7/8 | states with a line of k >= 4 | lowered by base | group alone | shuffles+group | GROUP ONLY (not base) | neither |
|---|---|---|---|---|---|---|---|---|
| <3,3,4>: 355 at 29, 1031 at 30 | 421 / 21 / - | 43,790 / 6,264 / 384 / 162 / - / - | 1324 of 1386 (96 %) | 668 | 290 | 461 | **0** | 718 |
| <4,4,4>: 2928 at 49..56 (278 at 49) | 1348 / 119 / 6 | 202,394 / 29,084 / 3,901 / 658 / 57 / 6 | 2650 of 2928 (91 %) | 2385 | 1790 | 1986 | **0** | 543 |

`both` against `base`: 5 vs 2 and 26 vs 31 states lowered by one and
not the other, the noise of randomized tries.  Mean time per state:
base 49 / 19 ms, one group scan 0.23 / 0.39 ms (about 50 scans per
guided round, which is the 2x slowdown measured on the Strassen^2
start), 200 shuffles 34 / 49 ms.

Verdict: the exact re-decomposition of every group whose factors span a
subspace of dimension <= 2 never opens a state that flips and merges
cannot open, on either format, at the funnel bottom or above it; it
re-routes reductions the engine finds anyway and costs 30-50 % of the
throughput.  The structures are not rare (tens of thousands of k >= 4
lines), they are just not where the obstruction is.  The next step on
this line, if ever, is planes (dimension 3: a 3-slice tensor rank, tiny
instances), and the probe is the cheap test to run before wiring it in.

Follow-up (2026-11-07, ../tomar_line/README.md): planes (dimension 3)
measured by the same probe with a SAT oracle, NEGATIVE at both formats;
Tomar's capacities as SAT constraints, NEGATIVE; projection as a seed
generator, POSITIVE at 4x4 (47 at 0 s against 54 from the trivial
start, a fourth rank-47 class at XOR count 171).
