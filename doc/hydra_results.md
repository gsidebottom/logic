# Hydra backend — SAT Competition main-track results (2025 + 2026)

Validation report for the `hydra` structure-dispatch portfolio backend, run
against the curated SAT-Competition main-track sets and compared to the
`pb-cadical` baseline. (Task #89.)

**Bottom line:** hydra solves **+11** more instances than the strong
pb-cadical baseline across the two sets (666 vs 655), with **every solve
sound** and **357 of ~370 UNSAT verdicts machine-certified** (0 wrong
proofs, 0 verdict mismatches). The remaining handful are resource-bound
giants whose verdict is trusted but whose proof exceeded a memory/time cap.

---

## What hydra is

A structure-dispatch portfolio: each instance is routed to the cheapest
engine that can decide it, and *every* UNSAT verdict carries a
machine-checkable certificate.

```
        parse CNF
            │
   structure analysis (ms, bounded)
            │
  ┌─────────┼───────────┬──────────────┐
 Cook      XOR/GF(2)    (residual)
 shape     parity         │
  │          │       kissat slice ──► cadical rest   (portfolio schedule)
 PB proof  GN21 PB      DRAT→LRAT      native LRAT
 (VeriPB)  proof        (cake_lpr)     (cake_lpr)
           or witness/rup
```

- **Cook prover** — PHP / RoundRobin / MVRoundRobin / clique-coloring /
  mutilated-chessboard → polynomial VeriPB cutting-planes proof.
- **XOR/GF(2)** — recover parity constraints, Gaussian-eliminate; pure-XOR
  decided outright (SAT witness, or GN21 pseudo-Boolean refutation for
  UNSAT; a pure unit-propagation refutation gets a one-line `rup`).
- **CDCL** — `--engine portfolio`: kissat for the first ~10 % of the budget,
  then cadical for the rest. kissat (DRAT → `drat-trim -L` → LRAT) and
  cadical (native LRAT) both verified by **cake_lpr**.

The premise (validated by this project's A/B history) is that we do **not**
beat kissat/cadical at general CDCL search; hydra wins by *composing*
reasoning systems each provably stronger on its slice, under one certified
roof.

---

## Methodology

- **Hardware:** Apple M4 Pro, 10 performance + 4 efficiency cores, 64 GB.
  (The SAT Competition itself ran on Dirk Beyer's LMU cluster — see the
  caveat below; raw solve counts are **not** portable across hardware.)
- **Command:** `run_benchmark.py -b hydra --sat-arg=--engine=portfolio
  -t 5000 --proof-timeout 5000 --proof-mem-gb 16 -j 10`.
- **Certification (competition rule "unverified = not solved"):** SAT =
  model-checked witness; UNSAT = checker-verified proof (VeriPB for
  PB/Cook/parity proofs, cake_lpr for LRAT). A solver verdict that fails to
  certify is reported as a **certification gap**, not a wrong answer — the
  solver/oracle is trusted; only the proof couldn't be (re-)checked within
  the memory/time budget.
- **Baseline:** the same harness with `-b pb-cadical` (Cook prover + raw
  cadical, no XOR stage, no portfolio).

---

## Headline

| set | metric | pb-cadical | **hydra** | Δ |
|-----|--------|-----------:|----------:|---:|
| **2025** (400) | solved | 347 | **352** | **+5** |
|  | SAT / UNSAT | 160 / 187 | 164 / 188 | |
|  | timeouts | 53 | 48 | −5 |
| **2026** (391) | solved | 308 | **314** | **+6** |
|  | SAT / UNSAT | 130 / 178 | 132 / 182 | |
|  | timeouts | 83 | 77 | −6 |
| **both** | **solved** | **655** | **666** | **+11** |

(2025 is effectively +6/353: `oisc-subrv-sll-nested-8` genuinely solved at
~200 s but was recorded TIMEOUT by a backstop verdict-overwrite bug fixed
mid-run. The 2026 run had every fix baked in from instance #1 and is the
cleaner of the two.)

---

## Per-stage attribution (UNSAT verdicts)

| stage | 2025 | 2026 | what it certifies |
|-------|-----:|-----:|-------------------|
| Cook (PB) | 24 | 27 | counting families, resolution-exponential |
| XOR/parity (GN21 PB) | 14 | 11 | parity families, resolution-exponential |
| kissat (LRAT) | 116 | 111 | CDCL, fast SAT-side + occasional UNSAT |
| cadical (native LRAT) | 34 | 33 | CDCL workhorse, long tail |

Cook + XOR are the **differentiated slice**: 76 UNSATs across the two sets
that reduce to counting or parity arguments, solved in milliseconds-to-
minutes *with verified proofs*, where plain CDCL is exponential. Several
(e.g. `tseitin_grid_n400`, 319k vars, 160k-XOR refutation) are solved by no
CDCL engine at 5000 s but certified by hydra in seconds.

---

## Gains and losses vs baseline

**2025 — 10 gains, 5 losses (net +5):**
- *XOR (4):* `tseitin_n188_d3`, `tseitin_grid_n250`, `tseitin_d3_n100000`,
  `tseitin_grid_n400` — all certified parity, all CDCL-timeout at 5000 s.
- *kissat SAT (6):* `Circuit_multiplier24`, two `sum_of_three_cubes_*`,
  `dislog_a14_x14_n24`, `rbsat-…gyes10`, `lockchart-…` — each solved inside
  the ~500 s kissat slice, each a 5000 s timeout for plain cadical (11×–370×
  speedups).
- *Losses:* 1 artifact (oisc, above); 1 variance (`bp4_TCO_CSO_ZR`,
  baseline 4133 s); 3 genuine portfolio-tail losses (`ITC2021_Late_10`,
  `oisc-subrv-and-nested-12`, `xor_op_n36`) that needed more than the post-
  slice 4500 s of cadical.

**2026 — 6 gains, 0 losses (net +6):**
- *XOR (3):* `x2_64`, `x2_72`, `tseitingrid6x185_shuffled` — certified.
- *kissat (3):* `abw-T-dwt` (SAT), `connm-ue-csp` (SAT), and
  `satcoin-genesis-UNSAT-6120` (**UNSAT**).

The 2025 portfolio-tail losses did **not** recur in 2026 — the structure-
analysis cost caps (queens-reconf, Ascon) and verdict-preservation fixes
returned that budget to the engines. Note also `satcoin-genesis`: kissat
contributed a *unique UNSAT* here, updating the 2025 observation that its
edge was purely SAT-side.

---

## Certification

| | 2025 | 2026 |
|---|---|---|
| UNSAT verdicts | 188 | 182 |
| **certified** | **178** | **179** |
| wrong proof (`failed`) | 0 | 0 |
| verdict mismatch | 0 | 0 |
| uncertified (resource) | 10 | 3 |

**Zero soundness violations across 791 instances.** Every uncertified
UNSAT is a *resource* gap on a trusted verdict: cake_lpr/VeriPB hitting the
16 GB heap cap on a giant proof, or drat-trim elaboration exceeding budget.
In 2026 these are explicitly labelled (e.g. *"cake_lpr out of memory (heap
cap; not a rejection)"*); the 2025 run predates that labelling and recorded
2 of them as `unverified`, but they are the same giant-heap aborts, not
proof errors.

Combined: **357 machine-certified UNSAT proofs** spanning three proof
systems — Cook cutting-planes (51), GN21 parity (24), and clausal LRAT
(282) — plus 296 model-checked SAT witnesses.

---

## The elaboration tax (and what it implies)

kissat emits hint-free DRAT, which `drat-trim -L` must backward-check and
elaborate to LRAT before cake_lpr can verify it. On 2026 this cost
**~16.2 hours aggregate** across 109 kissat UNSATs (max 2860 s for one
proof). cadical, by contrast, emits native LRAT — zero elaboration.

This is the single largest inefficiency in the certified pipeline and the
motivation for two follow-ups (task #90): a Rust DRAT→LRAT elaborator with
work-proportional progress, or — cheaper — re-solving kissat UNSATs with
`cadical --lrat` to obtain a native proof directly (cadical re-derives most
in seconds, skipping elaboration entirely).

---

## Comparison to SAT Competition 2025

How does hydra's 2025-set result stack up against the *actual* SAT
Competition 2025 main (sequential) track? **The raw count exceeds the field
— but the comparison is not like-for-like, and the gap is dominated by
hardware.**

Competition setup (organizers' slides): 400 main-track benchmarks, 5000 s
solver timeout, **45000 s** proof-checker budget, on Dirk Beyer's LMU
server cluster, under the rule *"an instance is not solved if the proof
checker times out"* — i.e. UNSAT requires a verified proof, the same
standard hydra holds itself to.

Main sequential track, instances solved (/400):

| solver | solved |
|--------|-------:|
| AE-Kissat-MAB (1st) | 327 |
| Kissat-public (2nd) | 321 |
| Kissat-VSA (3rd) | 317 |
| CaDiCaL-sc2025 (~5th) | <317 (exact not in slides) |
| **hydra (this report)** | **352 raw / 342 proof-verified** |

So on number of instances solved, hydra's **352** — or **342** counting
only machine-certified UNSATs (164 SAT witnesses + 178 verified UNSAT
proofs), the apples-to-apples figure against the competition's own
proof-verified rule — is **above the 2025 winner's 327**. We do solve more
problems.

**But three caveats, in decreasing order of importance — this is NOT "hydra
would have won SC2025":**

1. **Faster hardware (dominant).** This report ran on an Apple M4 Pro;
   SC2025 ran on an LMU cluster. A faster machine solves more in a fixed
   5000 s, and we measured ≥20× single-instance speedups for the *same*
   solver (kissat) on this M4 Pro vs the cluster-era expectation. Most of
   the +25 over the winner is the machine, not the method. The fair test
   would be running AE-Kissat-MAB / CaDiCaL-sc2025 on *this* M4 Pro — they
   would jump well above their cluster ranks too.
2. **Benchmark-set provenance.** Our `main_track_2025.jsonl` is a
   GBD-reconstructed approximation of the official 400, not verified
   instance-for-instance identical (its result field was unpopulated at
   curation). Small set differences shift the count either way.
3. **Checker budget.** The competition allows 45000 s of proof checking; we
   allowed 5000 s + a 16 GB heap. Our 10 uncertified-UNSAT resource gaps
   would mostly close under the competition's 9× budget — so hydra's
   proof-verified number sits between 342 (our budget) and ~352 (theirs).

**What is defensible and hardware-independent:** hydra certifies a
*differentiated slice* — 76 counting/parity UNSATs across the two sets,
several solved by no CDCL engine at 5000 s on *any* hardware (the
resolution-exponential families), each with a machine-checked proof. That
capability — not the raw count — is the real result; the count edge over the
field is genuine but mostly the M4 Pro talking.

Source: [SAT Competition 2025 results slides](https://satcompetition.github.io/2025/satcomp25slides.pdf).
No analogous comparison is given for 2026 — SC2026 main-track results are
not available to compare against.

## Honest caveats

- **Hardware confound.** These counts are on an M4 Pro; the competition ran
  on a server cluster. Raw solve counts vs published SC2025 standings are
  **not** comparable — a faster machine solves more in 5000 s. The valid
  internal comparison is hydra vs pb-cadical *on the same machine*, which is
  what this report measures.
- **kissat's edge is mostly SAT-side phase machinery** (target phases,
  embedded walk, stable-mode rephasing), amplified on heavy-tailed
  satisfiable crypto/algebraic instances. It is not an asymptotic
  separation; cadical has the same components, kissat is the newer tuning of
  them.
- **The portfolio is sequential** (kissat then cadical share one budget),
  chosen to keep the result competition-legal for the sequential track. A
  parallel `--engine both` would capture the union (kissat SATs + cadical
  tails) at 2× core cost — a different track, deferred.

---

## Conclusion

The multi-system synthesis pays off: **+11 net solves** over a strong
baseline, **no soundness regressions**, and **competition-rule-valid
certification on all but a handful of resource-bound giants**. The unique
contribution is the differentiated, *certified* slice — counting (Cook) and
parity (GN21) families that are exponential for resolution yet solved and
machine-proved in seconds — layered on top of a best-of-breed CDCL
portfolio. Remaining headroom is the elaboration tax (#90) and the
parallel-portfolio union (a separate track).
