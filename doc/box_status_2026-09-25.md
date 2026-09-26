# Where boxes stand (2026-09-25)

A status of the box technology — table constraints propagated by GAC over
their rows, explained lazily, inside a CDCL search — after the work of
2026-09-17 … 25.  Every number below is in a `doc/data/boxes_*` file with its
protocol; the design is `doc/box_backend_design.md`.

## The claim, and what was built to test it

The bet: compiled structure — a cone of gates, a group of clauses the search
keeps failing on — propagates as a table what its clauses lose (§1 of the
design doc: the adder), and a CDCL search that carries such tables solves
what clause-only search does not.

Built and measured:

- **The box engine** (`sat -b boxes`): CDCL over clauses and tables, live-row
  masks cut by kill masks, lazy explanations (greedy / minimal / cover),
  learning, restarts, reduction, level-0 simplification with bounded
  variable elimination, DRAT/LRAT certification through drat-trim and
  cake_lpr.  Its CDCL core was brought to CaDiCaL 3.0.1's level on memory
  (peak 8.9 → 6.5 GB on a 40 M-clause instance, CaDiCaL 6.9 GB) and
  measured against it on throughput, branching and clause quality.
- **Cones from CNF** (`tools/cnf2boxes.py`): Tseitin gates read off a CNF,
  merged into cones of ≤ K inputs, compiled to projected tables; residual +
  tables = the formula, certified end to end.
- **Mined boxes** (`tools/mine_boxes.py`): groups of conflict-carrying
  clauses scored by GAC-over-UP gap, emitted additively or absorptively.
- **Boxes inside CaDiCaL** (`src/boxes/upprop.rs`, `sat -b cadical --boxes`):
  the same tables as CaDiCaL's IPASIR-UP external propagator — forced
  literals through `cb_propagate`, kill-cover reasons at analysis, dead
  tables as falsified external clauses, per-level undo.
- **Box-native formulas exported** (web app `/boxes/export`): any jq box
  formula as residual + tables + expanded CNF, so the SLP windows, matmul
  schemes and waerden rows run through the same CLI arms.
- **A selection rule** (`tools/select_cones.py`): keep the cones whose table
  forces interface literals unit propagation over the cone's own clauses
  does not (gated on a full adder: 10% win rate; an XOR tree: 0).

## What the measurements say

| question | answer | where |
|---|---|---|
| Does branching on box constrainedness (EFF) find the failing box? | No: the failing box is the most constrained on 0–2% of conflicts, "tight half" ~50% — no signal (29 cone instances). | `boxes_eff_study_2026-09-18` |
| Do mined boxes convert a propagation gap into time? | No. Additive boxes fire on 0.55% of table conflicts (their clauses get there first); absorptive boxes fire 3× more often and are 7% slower. | `boxes_mined_*`, `boxes_absorptive_mining_2026-09-19` |
| Do cones help our engine? | Only where the tables carry the conflicts: pyhala-braun-sat 143 → 29 s (77% of conflicts in tables), level with CaDiCaL; ISCAS 3× slower; no timeout becomes a solve. | `boxes_step1_cones_2026-09-24` |
| How does our core compare to CaDiCaL's? | Fewer conflicts on 13/20 balanced instances (geomean 0.25×) — level-0 simplification, ours; 1.7× slower per conflict at scale; on the 76 we cannot solve, nothing known. | `boxes_balanced_suite_2026-09-21` |
| Where is the rate gap? | Propagation is 93% of our time vs 66%; per conflict 76 vs 24 µs on set-covering = 1.8× more propagations per conflict (search shape) × 1.8× per propagation (long-clause rescans, three accesses per clause visit). Position saving halves the steps but perturbs the search; not adopted. | `boxes_profile_2026-09-22` |
| Is it branching? | No: VMTF (queue), stable/focused alternation, stable-only, target phases — all neutral or negative on the median; CaDiCaL loses 1.47× without VSIDS. | `boxes_branching_2026-09-22` |
| Is it clause quality? | Partly: CaDiCaL's learned clauses are 2–2.5× shorter on the long searches. Shrinking (CaDiCaL-faithful, drat-trim verified) is the one lever found — set-covering 0.43× conflicts, 5× wall, faster than CaDiCaL there — instance-dependent, median 1.0, kept as an option. | `boxes_clause_quality_2026-09-23` |
| Is adding the boxes to CaDiCaL a win? | Over our engine: everywhere, 13/14 box-native rows and the factoring cones, up to two orders of magnitude — the core is the difference. Over plain CaDiCaL: the multiplier cones (toughsat 108.8 → 50.2 s, ezfact64_6 21 → 18 s) and small satisfiable windows by tenths of a second; 2–40× worse on the rest. Small tables are clauses; observed variables are frozen. | `boxes_step2_cadical_boxes_2026-09-24` |
| Does selecting the cones fix that? | Within trajectory noise: the 0-cone control arms differ from plain by 2–4× on satisfiable factoring instances, and no arm beats that spread. The UNSAT instance is monotone in the number of frozen cone variables. | `boxes_step3_selection_2026-09-25` |

Two corrections to earlier records: the box-native "2–25× faster than
CaDiCaL" rows came from the web app's hybrid (matrix-method path enumeration
with the engine completing prefixes against tables), not from CDCL over
residual + boxes, which loses those rows to plain CaDiCaL; and
"throughput is not the gap" (1.06× on the old 22-instance corpus) was a
small-instance artifact — at competition scale it is 1.7×.

## Conclusions

1. **The CDCL core matters more than the tables.**  CaDiCaL's core carrying
   our tables beats our core carrying our tables almost everywhere it was
   tried.  Our core's genuine advantage is level-0 simplification, not boxes.
2. **Tables pay where they absorb structure clause propagation loses — wide
   arithmetic cones — and nowhere else.**  A four-row table over five
   variables is four clauses; watched propagation with elimination free on
   every variable beats a table oracle over it.  The adder of §1 was finally
   measured end to end: 2.2× on toughsat's multiplier cones inside CaDiCaL.
3. **The interface bounds the win.**  Every observed variable is frozen
   against elimination and inprocessing; every table propagation is a
   callback with a reason of 5–9 literals built at analysis.  On the UNSAT
   factoring instance, more cones is monotonically worse.
4. **Search guidance from boxes does not exist as hoped.**  Constrainedness
   does not predict failure; additive boxes are redundant by construction;
   absorptive ones fire but do not speed up.
5. **The engine's core tuning is at diminishing returns.**  Every CaDiCaL
   feature above the noise floor is implemented; branching and phases are
   exhausted; shrinking is the one instance-dependent lever.

## What would change the picture, cheapest first

- **A variance-controlled factoring run** (several clause shuffles per arm,
  medians; ~12 h): the only way to know whether cones-in-CaDiCaL is a win on
  that family or the 2.2× is one trajectory.  Expected: null on SAT, loss on
  UNSAT.
- **A native table propagator inside CaDiCaL's propagate loop** rather than
  IPASIR-UP: no callback, no freezing, tables watched like clauses.  It is
  the experiment that separates "tables lose to clauses" from "the
  interface loses to clauses".  *Done 2026-09-26, see the addendum below:
  tables lose to clauses.*
- **The web app's hybrid, measured properly**: the matrix-method search with
  table completions is where box-native rows won; it was never run through
  the verdict-checked harness against CaDiCaL on the same formulas.
- **The 76 balanced instances we cannot solve**: cones inside CaDiCaL on the
  arithmetic families among them (hardware-verification, multiplier
  families) at 600 s, scored on newly solved.

## Addendum (2026-09-26): the native table propagator, done

`sat -b cadical --boxes … --boxes-native` puts the tables inside CaDiCaL's
propagate loop (`vendor/cadical-3.0.1/src/propagate.cpp`; data in
`doc/data/boxes_native_propagator_2026-09-26.txt`).  Two defects the
brute-force gates could not see: CaDiCaL's variable compaction renumbered
the tables' variables at 2000 conflicts (segfaults, "UNSAT" at 2002
conflicts, wrong models — compaction is off while tables exist, which by
itself swings satisfiable trajectories 4× either way), and visiting a table
at every assignment pre-empted the learned clauses and installed 53 reason
clauses per conflict (626 µs per conflict; visiting at the fixpoint of
clause propagation, as CaDiCaL asks an external propagator, gives 109).

The verdict, at equal conflict budgets and over 21 rows: **the interface
was not the loss.**  Native tables cost what IPASIR-UP tables cost, within
20 %; freezing costs nothing; both table arms are 1.5–2× plain per conflict
wherever the tables fire and level with plain where they do not.  Wall-clock
wins over plain (pyhala-sat 9.8 vs 24.6 s, 24bits 88 vs 104 s, the step-2
toughsat rows) are satisfiable-instance trajectories; every unsatisfiable
row loses 2–4×.  The hook is 4–28 % of a cone run and 72 % of a waerden run
(1900 table visits per conflict at 20 ns), so a compact-table hook would
trim it, not close it: the rest is the search doing 1.4× the propagations
per conflict through a residual whose structure the learned clauses
rediscover.  Small tables are clauses.  What remains open for tables is the
one thing this corpus cannot show — a trajectory that never converges
changed by cones on the 76 unsolved balanced instances, scored on solves.

## What to keep regardless

The measurement infrastructure paid for itself this fortnight and is worth
more than any single result: the family-balanced study set with recorded
verdicts (`tools/gbd/study_set.py`), the conflict-scored, verdict-checked A/B
harness (`night/suite.py`, `ab_search.py`), the propagation-work counters
(`BOXES_COUNT_VISITS`) and CaDiCaL's counters through the shim, the memory
checkpoints after `malloc_zone_pressure_relief` (`BOXES_MEM_REPORT`), the
brute-force gates on every propagator, and the traps written into memory: a
verdict check that flags correct answers (three times), a masked build, zsh
`env $var`, a treatment that never reached the system, and macOS charging
freed memory and uncharging copied memory.
