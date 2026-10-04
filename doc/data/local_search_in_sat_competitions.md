# Local search in the SAT Competitions, 2021-2026

Compiled 2026-10-04 for the question: how many instances of recent
competitions did local search solve much faster than CDCL, and were
local-search-capable solvers entered continuously and competitive?

Sources (downloaded with Greg's approval into `sat_benchmarks/sc2022/` and
`sat_benchmarks/sc_results/`): per-instance results for 2022 (main and
anniversary), 2023, 2024 and 2026 (`scores.csv`); 2025 published no
per-instance results, only the cactus coordinates behind its slides; solver
descriptions from the proceedings of 2021-2025 (2026 has none yet). The
2025 and 2026 `results.html` pages are stale copies of 2024's; their
rankings come from the slides and the data.

## Instance-level: one entrant at least 10x faster than every other

Instances where the fastest entrant was at least ten times faster than the
second (the second taking at least 60 s), from `rare.py` in the session
scratchpad. Which engine inside a solver found the answer is not recorded;
"local-search-heavy" means the solver's description makes local search a
central feature (class 2 below).

| year | such instances | SAT | by a local-search-heavy solver |
|---|---|---|---|
| 2022 anniversary (5,355) | 34 | 32 | 12 (kissat-els-v1/v2, LSTech_Maple, LStech-Maple-HyWalk, Kissat_MAB-HyWalk) |
| 2022 main | 2 | 2 | 2 (Kissat_MAB-HyWalk, kissat-els-v2) |
| 2023 main | 4 | 0 | 0 (symmetry breaking, XOR reasoning) |
| 2024 main | 10 | 2 | 0 |
| 2025 main | no per-instance data | | |
| 2026 main | 9 | 1 | 0 |

Satisfiable instances solved by at most two entrants (2022-2024) or two
author groups (2026): 2022 anniversary 60, 19 of them involving a
local-search-heavy solver; 2026 38, owned mostly by LymphoSAT (17; AI track,
"over 100 family-specific LLM-generated solvers using mostly specialized
preprocessing", 2026 slides) and kissat-sup (12; experimental track); the
possibly local-search line Kissat-MAB-HyPre owns 2.

Examples from 2022: sgen4-sat-280-8, kissat-els-v1 168 s against 2,767 s;
sgen3-n260, kissat-els-v2 52 s against 1,748 s; vmpc_36,
LStech-Maple-HyWalk 206 s against 3,954 s; Schur_160_5_d28, kissat-els-v1
120 s against 1,280 s.

Walking heavily everywhere cost more than it won (2022 anniversary, full
set): kissat-els-v1 (walkeffort 1000) solved 3,920 at PAR-2 3012 against
kissat-sc2022-light's 4,006 at 2867; head to head it solved 79 instances
light did not (68 SAT) and lost 165 (89 UNSAT), 17% slower on shared UNSAT
and 8% on shared SAT.

## Entrants by local-search use (research agent's report)

# Local search in SAT Competition main tracks, 2021–2026

## Summary

- **Local-search-heavy entrants were common in 2021–2022 and rare afterwards.** Class 2 (light and inherited cases included) covered 19/45 main-track entrants in 2021 and 21/52 in 2022. In 2023 it was 18/42, but only three of those described an LS change themselves: Kissat_MAB_DeepWalk+, Kissat_MAB_Rephases and AMSAT. Later counts were 3/14 in 2024, 2/22 in 2025 (both only the hKis `--walkinitially` flag) and 2/19 in 2026 (a guess, with no description available).
- **2022 is the high-water mark.** The top three by PAR-2 were all class 2: Kissat_MAB-HyWalk, kissat_inc and kissat_pre. All three are Kissat_MAB derivatives with moderate LS changes.
- **The heavy LS lines stopped appearing after 2022–2023:**
  - LSTech-named entrants: last seen 2022.
  - kissat-els: 2022 only.
  - kissat_cf, Kissat_relaxed and Kissat_cfexp (branching from LS conflict frequency): last seen 2022.
  - HyWalk derivatives and DeepWalk: last seen 2023.
  - CCAnr-in-CDCL: continued only through AMSAT (2023, 2024; amSAT is described in 2025 but is not in the ranking).
- **Top-three finishes after 2022 were weak cases:**
  - 2023: the runners-up, Kissat_MAB_prop (ranks 2–4), only inherit kissat_pre's LS initialisation. They won on UNSAT.
  - 2024: third place went to hKis-bva, whose only LS-specific change is `walkinitially=true`. It beat BreakID-Kissat by 0.62 PAR-2.
  - 2026: Kissat-MAB-HyPre, from the HyWalk author's group, was 3rd by mean score and 2nd on the slides. It has no description.
- **Raising walk effort alone did not pay.** kissat-els-v1 (`walkeffort` 1000) finished 34/52 in 2022, and Kissat_MAB_DeepWalk+ (5× walk rounds on one rephase) finished 26/42 in 2023. HyWalk's per-instance choice among {no walk, default, 5× walk} won 2022.
- **MiniSat/Maple-based CCAnr hybrids never finished near the top overall:** lstech_maple 13/45, LSTech_Maple 50/52, AMSAT 17/42 then 10/14. On SAT-only PAR-2, however, lstech_maple was 2nd in 2021.
- **No pure SLS solver (class 3) entered any main track from 2021 to 2026.** SLS appears only as workers inside parallel or cloud portfolios: YalSAT/CCAnr in Mallob, Painless and PRS.
- **Stock Kissat absorbed LS ideas, then stopped changing them:**
  - 2021: walker cache and strategy rotation (SC21 p.10).
  - 2022: "initial local search through propagation", i.e. warmup, citing Cai's ReasonLS (SC22 p.10).
  - 2023–2025: the descriptions mention no LS changes.

## Conventions

- **Ranks** exclude the VBS (the 2022–2024 results pages list the VBS as rank 1) and are by PAR-2.
- **"Class 2 (light)"** means a configuration-level or single-call LS change only, for example one extra initial walk.
- **"(inh.)"** means the entrant's own description is silent on LS, but its stated base solver's description has the LS feature. I assume the feature was kept.
- **"(inferred)"** means the year's description is silent, and the classification rests on the same line's earlier descriptions.
- **Citations** are proceedings pages:
  - SC21: B-2021-1, hdl 10138/333647.
  - SC22: B-2022-1, the local `sc2022/proceedings.txt`, identical to the Helda PDF.
  - SC23: the final Helda version, hdl 10138/563824. Its page numbers match the local draft.
  - SC24: B-2024-1, hdl 10138/584822.
  - SC25: DOI 10.34726/10379.
- **Ranking sources:**
  - 2021–2024: satcompetition.github.io/<year>/results.html. For 2023 I reproduced the page exactly from the local `results_main_detailed.csv`.
  - 2025: the slides give the top 3. Ranks 4–22 are recomputed from the cactus data in `2025/main-ALL.tex`; this reproduces all three slide values exactly (2264.73/327, 2423.38/321, 2478.45/317).
  - 2026: mean of `score` per solverid in `2026/scores.csv`.

---

## (a) Class-2/3 entrants per year

### 2021: main track, 45 ranked solvers

Winner: **Kissat_MAB**, 3194 / 296 solved, class 1 (MAB between VSIDS and CHB). No entrant was class 3.

| Solver | Class | Technique | Source | Rank/45 | PAR-2 | Solved |
|---|---|---|---|---|---|---|
| hKis_unsat | 2 (light) | Kissat hack; config `target=1 walkinitially=1 chrono=1` (one initial walk) | SC21 p.26 | 6 | 3435 | 286 |
| kissat_cf | 2 | Kissat with embedded YalSAT-style walker; LS conflict frequency bumps VSIDS (100×freq every 20 restarts) | SC21 p.42 | 7 | 3508 | 282 |
| lstech_maple | 2 | Relaxed_newTech successor: no-backtrack stage builds a full assignment; CCAnr (clause-state CC) called every δ restarts; LS phases | SC21 p.42 | 13 | 3646 | 277 |
| ParaFROST | 2 | own WalkSAT LS used for rephasing **and** called in every first MDM round to pick multiple decisions | SC21 pp.32–33 | 16 | 3677 | 278 |
| Cadical_SCAVEL01 | 2 | CaDiCaL-SC2020 with more SLS flips on small (<3000 vars) instances, to solve directly | SC21 pp.19–20 | 19 | 3798 | 274 |
| CaDiCaL_rp | 2 (light) | CaDiCaL with Relaxed-style probabilistic choice among saved, best and LS phases | SC21 p.42 | 20 | 3841 | 272 |
| Relaxed_LCMDCBDL_SCAVEL01 | 2 (inh.) | Relaxed_LCMDCBDL_newTech (relaxed CDCL + ccnr) plus active backtrack | SC21 pp.19–20 | 21 | 3843 | 269 |
| SLIME_hess_no_rnd | 2 | "HESS": greedy one-variable-at-a-time flip search minimising falsified clauses ("MaxSAT oracle") to reset phases at restarts | SC21 p.37 | 23 | 3896 | 270 |
| SLIME_hess_rnd | 2 | same, random initial polarities | SC21 p.37 | 24 | 3978 | 267 |
| Maple_MBDR_Cent_PERM_10K | 2 (inh.) | Relaxed_newTech base plus centrality-based clause retention | SC21 p.21 | 26 | 4000 | 266 |
| Maple_MBDR_Cent_PERM_75K | 2 (inh.) | same | SC21 p.21 | 29 | 4047 | 264 |
| Relaxed_LCFTP | 2 (inh.) | Relaxed_newTech base plus learnt-clause bumping change | SC21 p.14 | 33 | 4092 | 262 |
| Cadical_SCAVEL02 | 2 | cadical-alluip-trail with more SLS flips on small instances | SC21 pp.19–20 | 36 | 4136 | 263 |
| Relaxed_LCFTP_V3 | 2 (inh.) | parameter variant | SC21 p.14 | 37 | 4157 | 258 |
| Relaxed_LCFTP_V2 | 2 (inh.) | parameter variant | SC21 p.14 | 38 | 4179 | 258 |
| Relaxed_LCMDCBDL_BLB | 2 (inh.) | Relaxed_newTech base plus backtrack-level restarts | SC21 p.14 | 39 | 4180 | 255 |
| Relaxed_LCMDCBDL_SCAVEL02 | 2 | Relaxed_newTech base plus SCAVEL II.A–D, including more ccnr flips on small instances | SC21 pp.19–20 | 40 | 4465 | 249 |
| Maple_MBDR_BJL6_Tier2 | 2 (inh.) | Relaxed_newTech base plus backjump learning | SC21 pp.21–22 | 42 | 6572 | 150 |
| Maple_MBDR_BJL7_Local | 2 (inh.) | same | SC21 pp.21–22 | 43 | 6620 | 148 |

SAT-only PAR-2 (results-page columns): lstech_maple was **2nd** (2358 / 144), behind Kissat_MAB (2222). kissat_cf was 5th and Relaxed_LCMDCBDL_SCAVEL01 6th.

### 2022: main track, 52 ranked solvers

Winner: **Kissat_MAB-HyWalk**, 3334.22 / 290, **class 2**. SC23 p.29 calls it "the winner of the main-track".

| Solver | Class | Technique | Source | Rank/52 | PAR-2 | Solved |
|---|---|---|---|---|---|---|
| Kissat_MAB-HyWalk | 2 | per-instance hybrid of Kissat_MAB, Kissat_MAB without walking, and Kissat_MAB with walk rounds ×5 (selection as in LStech-Maple-HyWalk's decision tree) | SC22 pp.20–21 | **1** | 3334.22 | 290 |
| kissat_inc | 2 | Kissat_MAB plus LSTech-Maple's rule for generating LS initial assignments, used to manage target phases | SC22 pp.37–38 | **2** | 3351.93 | 290 |
| kissat_pre | 2 | kissat_inc plus RC and Fourier–Motzkin elimination preprocessing | SC22 p.38 | **3** | 3380.17 | 288 |
| SeqFROST-ERE-All | 2 (light) | own LS improves MDM decision phases, once at the initial MDM call | SC22 pp.30–31 | 11 | 3534.52 | 282 |
| SeqFROST-NoExtend | 2 (light) | same | SC22 pp.30–31 | 13 | 3578.23 | 280 |
| LSTech_CaDiCaL | 2 | LSTech-Maple probabilistic (LS-based) rephasing on CaDiCaL, plus watch-sat | SC22 pp.37–38 | 17 | 3631.17 | 279 |
| kissat-els-v3 | 2 | ccnr (from lstech_maple) replaces the Kissat walker, on irredundant clauses; decision phases as LS init | SC22 p.19 | 18 | 3636.50 | 279 |
| kissat-els-v2 | 2 | unit-propagation walk initialisation (`--walkup`) | SC22 p.18 | 23 | 3677.45 | 276 |
| hKis-unsat | 2 (light) | `--target=1 --walkinitially=true --chrono=true` | SC22 p.24 | 24 | 3679.89 | 273 |
| kissat-els-v4 | 2 | ccnr plus UP initialisation | SC22 p.19 | 28 | 3754.58 | 274 |
| hKis-sat | 2 (light) | `--sat --walkinitially=true` | SC22 p.24 | 31 | 3820.19 | 268 |
| Kissat_cfexp | 2 | branching score plus expSAT score plus LS conflict-frequency (CF) score | SC22 pp.39–40 | 32 | 3858.45 | 269 |
| kissat-els-v1 | 2 | `--walkeffort=1000` (20× default), vivifyeffort=1, sweep=false | SC22 p.18 | 34 | 3913.29 | 266 |
| kissat_relaxed | 2 | Kissat-cf plus relaxed CDCL: a promising partial assignment is extended without conflict analysis, then the walker is called (3 restarts × 500 steps) | SC22 p.35 | 35 | 3947.96 | 265 |
| LStech-Maple-FPS | 2 | LSTech-Maple with FPS (look-ahead sampling) replacing CCAnr | SC22 p.20 | 37 | 4111.75 | 257 |
| LStech-Maple-HyWalk | 2 | LSTech-Maple with a decision tree choosing among 6 walkers (CCAnr, BandSAT, FPS, SimpleWalk, FS, BF) | SC22 pp.20–21 | 40 | 4167.32 | 254 |
| LStech-Maple-BandSAT | 2 | LSTech-Maple with BandSAT (bandit over falsified clauses) replacing CCAnr | SC22 p.20 | 44 | 4284.55 | 249 |
| MergeSat 4.0-rc-rc2 | 2 | default MergeSat (CCNR SLS engine used during search), system libm | SC22 pp.25–26 | 47 | 4401.24 | 249 |
| LSTech_kissat | 2 | Kissat plus CCAnr for phases, LSTech probabilistic rephasing, RC | SC22 p.38 | 48 | 4412.64 | 251 |
| MergeSat 4.0-rc-rc1 | 2 | default MergeSat with CCNR SLS | SC22 pp.25–26 | 49 | 4464.11 | 245 |
| LSTech_Maple | 2 | improved lstech_maple: BMS in CCAnr, LS-entry filter, LS-based probabilistic phasing, LS conflict frequency in branching | SC22 p.37 | 50 | 4564.46 | 236 |

SAT-only PAR-2: SeqFROST-NoExtend 1st (1709.42), SeqFROST-ERE-All 2nd, kissat_inc 3rd, HyWalk 4th, kissat_pre 5th, so the SAT-only top five were all class 2. kissat-els-v1 was 32nd and LSTech_Maple 44th. MergeSat rc3, the "No SLS" configuration, is class 0 and ranked 51st.

### 2022: anniversary track, 30 ranked solvers

Winner: **Kissat_MAB_ESA**, 2806.15 / 4029, class 1.

| Solver | Class | Source | Rank/30 | PAR-2 | Solved |
|---|---|---|---|---|---|
| kissat_inc | 2 | SC22 p.38 | 5 | 2833.12 | 4012 |
| Kissat_MAB-HyWalk | 2 | SC22 pp.20–21 | 8 | 2856.95 | 3991 |
| kissat-els-v2 | 2 | SC22 p.18 | 10 | 2896.12 | 3986 |
| hKis-unsat | 2 (light) | SC22 p.24 | 11 | 2949.92 | 3954 |
| SeqFROST-NoExtend | 2 (light) | SC22 pp.30–31 | 13 | 2974.96 | 3943 |
| kissat-els-v1 | 2 | SC22 p.18 | 15 | 3011.92 | 3921 |
| kissat_relaxed | 2 | SC22 p.35 | 18 | 3083.58 | 3878 |
| LStech-Maple-HyWalk | 2 | SC22 pp.20–21 | 22 | 3288.58 | 3770 |
| LSTech_Maple | 2 | SC22 p.37 | 23 | 3290.05 | 3775 |
| MergeSat 4.0-rc-rc1 | 2 | SC22 pp.25–26 | 24 | 3377.83 | 3733 |
| MergeSat 4.0-rc-rc2 | 2 | SC22 pp.25–26 | 27 | 3413.01 | 3711 |

### 2023: main track, 42 ranked solvers

Winner: **SBVA-CaDiCaL**, 3274.01 / 284, class 1.

| Solver | Class | Technique | Source | Rank/42 | PAR-2 | Solved |
|---|---|---|---|---|---|---|
| Kissat_MAB_prop_pr-no_sym | 2 (inh.) | built on Kissat_Pre (SC22), so it carries kissat_inc's LS-init rule; own changes are a propagation-based MAB reward, PR clauses and partial symmetry breaking; its description is silent on LS | SC23 pp.16–17 | **2** | 3596.73 | 272 |
| Kissat_MAB_prop | 2 (inh.) | same | SC23 pp.16–17 | **3** | 3614.43 | 270 |
| Kissat_MAB_prop-no_sym | 2 (inh.) | same | SC23 pp.16–17 | 4 | 3652.44 | 267 |
| AMSAT_ | 2 | MiniSat/lstech_maple base with calls to CCAnr; adds failed/implied/equivalent literal detection and other techniques | SC23 pp.32–33 | 17 | 4116.23 | 249 |
| SeqFROST-NoExtend | 2 (light) | LS once at the initial MDM call | SC23 pp.21–22 | 18 | 4180.95 | 251 |
| SeqFROST | 2 (light) | same | SC23 pp.21–22 | 19 | 4222.91 | 248 |
| SeqFROST-ERE-All | 2 (light) | same | SC23 pp.21–22 | 20 | 4254.86 | 247 |
| Kissat_MAB_Rephases | 2 | combined rephase policies, including DeepWalk (5× LS rounds) | SC23 p.27 | 21 | 4311.36 | 246 |
| kissat-hywalk-exp | 2 (inh.) | Kissat_MAB-HyWalk plus bounded random exploration | SC23 pp.28–29 | 24 | 4548.90 | 234 |
| kissat-hywalk-gb | 2 (inh.) | HyWalk plus glue bumping | SC23 pp.28–29 | 25 | 4555.19 | 235 |
| Kissat_MAB_DeepWalk+ | 2 | rephase policy OI(BW BOBW BIBW B#BDBF)^ω, where D is a walk with 5× LS rounds | SC23 p.27 | 26 | 4577.75 | 233 |
| MergeSat-bve_semgates | 2 (inferred) | default MergeSat config, which used CCNR SLS in the SC21 p.30 and SC22 p.26 descriptions; the SC23 text is silent | SC23 pp.34–36 | 27 | 4591.08 | 233 |
| MergeSat-bve_gates | 2 (inferred) | same, with syntactic gates | SC23 pp.34–36 | 29 | 4651.73 | 229 |
| kissat-hywalk-exp-gb | 2 (inh.) | HyWalk plus DB and GB | SC23 pp.28–29 | 31 | 4663.67 | 228 |
| kissat_incsp | 2 (inh.) | kissat_inc plus prefetching; "no algorithmic changes" | SC23 pp.19–20 | 32 | 4732.05 | 228 |
| MergeSat-thread1 | 2 (inferred) | default MergeSat, 1 thread ("pretty close to the configuration used in 2021") | SC23 p.35 | 33 | 4750.55 | 228 |
| Kissat_Inc_ESA | 2 (inh.) | ESA in kissat_inc | SC23 p.32 | 35 | 4794.27 | 225 |
| hKis-unsat | 2 (light) | `--target=1 --walkinitially=true --chrono=true` | SC23 p.37 | 36 | 4862.98 | 219 |

The results page shows two rows named "KissatMab-Conflict". The local CSV identifies 4323.33 as Kissat_MAB_Conflict and 4610.94 as Kissat_MAB_Conflict+. Both are class 1, because walking is unchanged.

SAT-only PAR-2: AMSAT was 6th, the best class-2 entrant. Kissat_MAB_prop variants were 26th, 29th and 33rd on SAT-only but 1st–3rd on UNSAT-only. DeepWalk+ was 30th and Rephases 19th.

### 2024: main track, 14 ranked solvers

Winner: **kissat-sc2024**, 2788.13 / 306, class 1.

| Solver | Class | Technique | Source | Rank/14 | PAR-2 | Solved |
|---|---|---|---|---|---|---|
| hKis-bva | 2 (light) | SBVA plus Kissat 3.1.1 hack with `target=1 walkinitially=true chrono=true` (mapping of config to name inferred; "p" = psids) | SC24 pp.25–26 | **3** | 3461.15 | 285 |
| AMSAT_RGC | 2 | AMSAT (CCAnr) plus less frequent garbage collection | SC24 pp.15–16 | 9 | 3631.69 | 279 |
| AMSAT | 2 | lstech_maple base with CCAnr calls | SC24 pp.15–16 | 10 | 3641.2 | 278 |

SAT-only PAR-2: hKis-bva 3rd (1997.14), AMSAT 7th, AMSAT_RGC 8th.

### 2025: main track, 22 ranked solvers

The slides count 26 sequential solvers; the plots show 22.

Winner: **AE-Kissat2025-MAB**, 2264.73 / 327, class 1 (LLM-evolved bump, rescale and MAB code; no LS).

| Solver | Class | Technique | Source | Rank/22 | PAR-2 | Solved |
|---|---|---|---|---|---|---|
| hKis2-psids | 2 (light) | SBVA plus hKis on Kissat-2024, `psids=1 target=1 walkinitially=true chrono=true` | SC25 p.27 | 19 | 3199.84 | 289 |
| hKis-sbva | 2 (light) | SBVA plus hKis (2024 version), `target=1 walkinitially=true chrono=true` | SC25 p.27 | 20 | 3323.35 | 284 |

No other ranked 2025 entrant changes local search. The proceedings also describe amSAT, from the AMSAT/CCAnr group (SC25 pp.30–31), but its text does not mention CCAnr and it does not appear in the ranking.

### 2026: inferred, no proceedings

There are 19 `[main]` solverids, 33 including the `[main-ai]`, `[exp]` and `[exp-ai]` sub-tracks.

Winner: **anders_satsuma-iter-kissat[main]**, 3647.02 / 276, class 1 (inferred from Satsuma+Kissat, SC25 p.8).

| Solver | Class | Technique | Source | Rank (/19 main; /33 all) | Mean score | Solved |
|---|---|---|---|---|---|---|
| zheng_kissat-mab-hypre[main] | **guess 2, low confidence, no description** | Same first author as Kissat_MAB-HyWalk (2022) and DeepWalk+/Rephases (2023). The "MAB-Hy…" name suggests a HyWalk successor; "Pre" is unexplained. | inferred | 3 / 4 (slides' per-team ranking: **2nd**) | 3996.29 | 255 |
| zheng_kissat-mab-hypre-v2[main] | guess 2 | same | inferred | 4 / 5 | 3997.28 | 255 |
| zheng_kissat-mab-hypre-evolve[main-ai] | guess 2 | AI-tuned variant | inferred | – / 6 | 4009.70 | 255 |
| zheng_kissat-mab-hypre-satlution[main-ai] | guess 2 | AI-tuned variant | inferred | – / 7 | 4066.84 | 253 |

SAT-only, recomputed from scores.csv: Kissat-MAB-HyPre was 2nd among `[main]` (3445.92 / 134), behind satsuma-iter-ae-kissat-mab (3430.95). This matches the slides. The AI-track Lymphosat was best overall on SAT-only (2813.50).

---

## (b) Class-1 and class-0 entrants

- **2021: 15 class 1, 11 class 0.**
  - Class 1 includes Kissat_MAB, Kissat_sc2021_sweep/default/sat, kissat_gb, kissat_crvr_gb, hKis, hKis_psids, CaDiCaL_sc2021, cadical_watch_sat, CaDiCaL_PriPro (+_no_bin), cadical_hack_gb and kissat_bonus. It also includes ParaFROST_NoMDM, which has its own CaDiCaL-style rephase walker and MDM off.
  - Class 0:
    - hCaD and hCaD_psids: CaDiCaL with `walk=0` (SC21 p.26).
    - Maple_simp21, optsat_R21 and optsat_m21: "we delete the local search solver for rephasing" (SC21 p.23).
    - SLIME_no_hess_no_rnd and SLIME_no_hess_rnd.
    - MapleSSV: random-walk exploration means random decisions plus UP, not SLS.
    - cms_expV_gbL: by description; see uncertainties.
    - CleanMaple and CleanMaple_PriPro.
- **2022 main: 21 class 1, 10 class 0.**
  - Class 1 includes Kissat_MAB_UCB, MOSS and ESA, ekissat-mab-db-v1/v2, ekissat-mab-gb-db, kissat-mab-gb, kissat-sc2022-bulky/hyper/light, the watchsat-lto pair, CaDiCaL_DVDL_V1/V2, CadicalReorder, Cadical_ESA, cadical-hack-gb, Kissat_adaptive_restart and hKis-psids.
  - Kissat-MAB-rephasing is class 1 but borderline: a bandit over rephase schemes that include the stock walk.
  - cadical_rel_Scavel has no 2022 description; I guessed class 1.
  - Class 0:
    - hCaD_V2 and hCaD_V1-psids (`--walk=false`).
    - MergeSat rc3 ("No SLS").
    - MapleLCMDistChrBt-DL-v3.
    - SLIME ×4.
    - glucose-reboot (no description; guessed).
    - IsaSAT.
- **2022 anniversary: 13 class 1, 6 class 0.** Class 1 includes the winner Kissat_MAB_ESA and kissat-sc2022-bulky. Class 0: glucose-reboot, SLIME ×2, hCaD_V1-psids, MapleLCMDistChrBt-DL-v3, IsaSAT.
- **2023: 22 class 1, 2 class 0.**
  - Class 1 includes SBVA-CaDiCaL/Kissat, MapleCaDiCaL ×4, PReLearn ×2, ReEncode, CaDiCaL_vivinst, kissat-3.1.0, TabularaSAT, Kissat_MAB_Conflict and BreakID-kissat.
  - Kissat_MAB_Conflict+ is class 1 but borderline: a Best phase is inserted after each Walk.
  - hKissatInc-unsat (Kissat-Inc with `--unsat`) is class 1; see uncertainties.
  - Class 0: IsaSAT and MiniSat+XorEngine (no description; guessed).
- **2024: 8 class 1, 3 class 0.** Class 1 includes kissat-sc2024, Kissat_MAB-DC (2nd), BreakID-Kissat, CaDiCaL 2.0 and hKis-pbva. Class 0: hCaD-bva and hCaD-pbva (`walk=false`), IsaSAT.
- **2025: 18 class 1, 2 class 0.** Class 1 includes AE-Kissat2025-MAB/bump/rescale, Kissat-public, Kissat-VSA, Kissat-CURE, Kissat-pred, CaDiCaL-sc2025, ULC ×4, Satsuma-Kissat-sc and Dynamiccadical. Kissat-MAB-CoRephase and Kissat-CoRephase-CoReward are class 1 but borderline: a MAB over rephase triples that all contain Best+Walk. Class 0: hCaD-sbva and hCaD-psbva (`walk=false`).
- **2026 `[main]`, all inferred: 15 class 1, 1 class 0, 1 unknown.**
  - Class 1: satsuma ×4, kissat-eda ×4, kissat-biere, cadical3, guo kissat-ae-eg/hucb, liang kissat-mab-da/lr-ds, cadical-xlc-freeze.
  - Class 0: isasat.
  - Unknown: zhenwei_mergesat. The name matches Manthey's CCNR-equipped MergeSat, but the authors are Zhenwei Yang et al., so I see no basis to infer LS.
  - Other sub-tracks: ding/gopalan AI-tuned Kissats are inferred class 1. Lymphosat, faraja_llmg and kissat-sup are unknown.

---

## (c) Continuity

Local-search-capable entrants were present every year, but the substantial ones form a 2021–2022 wave that then faded.

**Lines that persisted:**
- The Relaxed/LSTech family (CCAnr inside MiniSat/Maple CDCL). In 2021 this was lstech_maple and ten third-party Relaxed_newTech derivatives (Relaxed_LCFTP ×3, Relaxed_LCMDCBDL_BLB, Relaxed_LCMDCBDL_SCAVEL01/02, Maple_MBDR ×4). In 2022 it was LSTech_Maple, LSTech_kissat and LSTech_CaDiCaL, plus Zheng's LStech-Maple-BandSAT, FPS and HyWalk.
- Its Kissat transplants: kissat_cf (2021); kissat_inc, kissat_pre, Kissat_relaxed and Kissat_cfexp (2022); and, by inheritance only, Kissat_MAB_prop, kissat_incsp and Kissat_Inc_ESA (2023).
- HyWalk: Kissat_MAB-HyWalk (2022), Chowdhury's kissat-hywalk-* and Zheng's DeepWalk+/Rephases (2023), and possibly Kissat-MAB-HyPre (2026).
- The CCAnr-in-MiniSat line via AMSAT (2023, 2024).
- MergeSat's CCNR engine (2022, inferred for 2023).
- hKis' one-flag `walkinitially` configuration, entered every year 2021–2025.

**When the heavy lines stopped appearing:**
- The last LSTech-named entrants were in 2022. The Cai group then moved to the parallel track (PRS 2023–2026, which runs YalSAT threads for initial phases, SC25 p.21).
- kissat-els (Huawei TCS) ran in 2022 only.
- The LS-conflict-frequency solvers (kissat_cf, Kissat_relaxed, Kissat_cfexp) ended in 2022.
- The HyWalk-derived and DeepWalk solvers ended in 2023.
- SCAVEL's SLS-flip boost and SLIME's HESS phase search were 2021 only.
- CCAnr hybrids ended with AMSAT in 2024.
- 2025's ranked field contains no LS-heavy solver at all.

**Top-three finishes:**
- Yes in 2022: all three top PAR-2 places went to LS-modified Kissat_MAB derivatives.
- Arguably in 2023: places 2–4 by inheritance only, with wins coming on UNSAT.
- Marginally in 2024: hKis-bva 3rd, with only an initial-walk flag.
- Possibly in 2026: Kissat-MAB-HyPre is 2nd per team and 3rd by score; its contents are unknown.
- Never in 2021 or 2025. In 2021 the best was hKis_unsat (6th, light), and kissat_cf was 7th.

The more competitive designs were Kissat-based and moderate: instance-adaptive walk effort, and an LS-derived initial assignment. Bolting stronger SLS engines (CCAnr, BandSAT, FPS) into MiniSat-family CDCL helped mainly on SAT instances (lstech_maple 2nd SAT-only in 2021) but never placed well overall.

---

## (d) Uncertainties

1. **Inheritance assumption.** The "(inh.)" classes assume the base's LS feature was kept: Kissat_MAB_prop ×3, kissat_incsp, Kissat_Inc_ESA, kissat-hywalk-*, and the Relaxed/Maple_MBDR derivatives. None of these descriptions confirm or deny it. Kissat-Inc's own LS change (SC22 p.38) is a target-phase and LS-initialisation rule, not a stronger walker.
2. **MergeSat 2023 is inferred.** Its default configuration "pretty close to 2021" is assumed to still use CCNR. Separately, MergeSAT 3.0 is described in SC21 p.30 (default uses CCNR) but does not appear in the 2021 main ranking.
3. **`--unsat` means no walking (my reading of Kissat's design, not the descriptions).** `--unsat` sets `stable=0`, and Kissat only rephases, and hence walks, in stable mode. This is why hKis-psids (2022/23), hKis-pbva (2024) and hKissatInc-unsat (2023) are class 1, despite the last being built on Kissat-Inc.
4. **hKis name-to-config mapping is inferred for 2024/2025** ("p" = psids). It is consistent with the psids configurations' weak SAT results.
5. **Stock-line LS changes are counted as class 1.** These are Kissat sc2021's walker changes and kissat-sc2022-bulky's warmup initialisation. On a literal reading of "new walk initialisation", kissat-sc2022-bulky (12/52 in 2022, 2/30 anniversary) would be class 2.
6. **Borderline class-1 rephase-schedule bandits:** Kissat-MAB-rephasing (2022), Kissat_MAB_Conflict+ (2023), and Kissat-MAB-CoRephase / CoRephase-CoReward (2025). They reorder or select rephase steps around the unchanged walker; none raise walk effort.
7. **cms_expV_gbL (2021)** is class 0 by its description. Its base, CryptoMiniSat 5.8, has its own SLS component in my background knowledge, which I did not verify here. If that counts, it is class 2 at rank 32/45.
8. **SLIME:**
   - 2021 HESS is a deterministic greedy flip search, which I counted as LS-guided rephasing.
   - The no-HESS variants claim a "simplified variation of RelaxedLCMDCBDLnewTech" techniques, so whether any LS remains is unclear.
   - In 2022, HESS selects among rephasing heuristics rather than flipping variables, so 2022 SLIME is class 0.
9. **SeqFROST/ParaFROST.** After 2021 the descriptions do not say whether the rephase walker is still run. Only the "once at initial MDM" use is stated.
10. **Cadical_SCAVEL01 (2021) is built on CaDiCaL-SC2020.** SC21 p.10 says that version failed to export LS assignments as phases. Its SLS-flip boost may therefore have had little effect (inference).
11. **No 2022 descriptions** for cadical_rel_Scavel (guessed 1) and glucose-reboot (guessed 0). No 2023 description for MiniSat+XorEngine (guessed 0).
12. **Local data gaps:**
    - `solver_lists.json` and `sc2022/main-seq.csv` list only MergeSat rc3. The official 2022 page also ranks rc1 and rc2 (class 2); I used the page.
    - 2025: 4 of the 26 sequential solvers on the slides are not plotted. These are probably among Kissat_Scavel_RS/2025, dilemma and amSAT, which are described in SC25 but unranked here.
    - 2026: the slides say 17 main-track solvers, but scores.csv has 19 `[main]` ids. The guo_* pair is absent from the slide plots, yet AE-kissat-HUCB appears 3rd in the slide's SAT table. I ranked all 19.
13. **2026 classes are inferences from names, authors and earlier lines.** The HyPre guess in particular is low confidence; a web search found no description. arXiv 2602.20829 (Yalun Cai et al., clause management, no LS) may underlie kissat-eda; this is unverified.
14. **Award places.** The official award order is per team: the 2026 slides skip same-team entries, and 2025's SAT table does too. I report raw PAR-2 ranks. For 2022, the per-team medal order is my inference (HyWalk, kissat_inc, then ekissat-mab-db-v1), not taken from an official list.
