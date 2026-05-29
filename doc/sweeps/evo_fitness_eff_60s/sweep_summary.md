# τ sweep on `evo_fitness.jsonl` (backend `eff`, timeout 60s)

## Per-τ totals

| τ | solved | timeout | mismatch | unknown | total CPU (solved) |
|---|--------|---------|----------|---------|--------------------|
| 0 | 5 | 40 | 0 | 0 | 2.9s |
| 0.5 | 5 | 40 | 0 | 0 | 0.9s |
| 1 | 6 | 39 | 0 | 0 | 16.9s |
| 2 | 6 | 39 | 0 | 0 | 17.1s |
| inf | 6 | 39 | 0 | 0 | 16.9s |

## Recommended τ

**`--eff-tau inf`** — solves **6** unique instances (wins 2 of them on fastest time; 16.9s total CPU on solved). Ranking criteria: most solved > most wins > lowest CPU.

| τ | solved | wins | CPU on solved |
|---|--------|------|---------------|
| inf | 6 | 2 | 16.9s |
| 2 | 6 | 1 | 17.1s |
| 1 | 6 | 0 | 16.9s |
| 0 | 5 | 2 | 2.9s |
| 0.5 | 5 | 1 | 0.9s |

## Best τ per family

| Family | solved | unsolved-by-any-τ | top τ (wins) |
|--------|--------|-------------------|--------------|
| (other) | 2 | 27 | 0 (2) |
| Steiner | 3 | 1 | 2 (1), inf (1), 0.5 (1) |
| WS-graph | 0 | 1 | — |
| crypto | 0 | 6 | — |
| frb (random) | 0 | 1 | — |
| x9/x10 | 1 | 3 | inf (1) |

## Per-problem results

| Problem | 0 | 0.5 | 1 | 2 | inf |
|---------|----------|----------|----------|----------|----------|
| 170055892 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 170058440 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 170059081 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 170153306 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 170222843 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 170223547 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 170225812 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| Break_04_04.xml | **SAT 0.014s** | SAT 0.199s | SAT 0.196s | SAT 0.202s | SAT 0.202s |
| Break_triple_04_06.xml | **SAT 0.013s** | SAT 0.018s | SAT 0.017s | SAT 0.018s | SAT 0.017s |
| SCPC-500-1 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| SCPC-500-12 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| SCPC-500-13 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| SCPC-500-14 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| SCPC-500-5 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| Steiner-15-7-bce | UNSAT 0.029s | UNSAT 0.011s | UNSAT 0.011s | **UNSAT 0.010s** | UNSAT 0.010s |
| Steiner-27-10-bce | TIMEOUT 60.0s | TIMEOUT 60.0s | UNSAT 16.10s | UNSAT 16.20s | **UNSAT 16.02s** |
| Steiner-45-16-bce | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| Steiner-9-5-bce | UNSAT 1.1ms | **UNSAT 0.8ms** | UNSAT 0.9ms | UNSAT 0.9ms | UNSAT 0.8ms |
| VanDerWaerden_pd_2-3-22_462 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| WS_500_16_90_70.apx_1_DC-ST | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| battleship-16-31-sat | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| battleship-24-47-sat | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| case16.normalised | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| case17.normalised | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| case20.normalised | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| case9 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| combined-crypto1-wff-seed-101-wffvars-500-cryptocplx-31-overlap-2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| combined-crypto1-wff-seed-102-wffvars-500-cryptocplx-31-overlap-2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| combined-crypto1-wff-seed-107-wffvars-500-cryptocplx-31-overlap-2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| combined-crypto1-wff-seed-115-wffvars-500-cryptocplx-31-overlap-2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| combined-crypto1-wff-seed-132-wffvars-500-cryptocplx-31-overlap-2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| combined-crypto1-wff-seed-3-wffvars-450-cryptocplx-40-overlap-2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| contest03-SGI_30_50_30_20_3-dir.sat05-440.reshuffled-07 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| frb35-17-5_ext | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| gto_p60c241 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| hid-uns-enc-6-1-0-0-0-0-14492 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| hid-uns-enc-6-1-0-0-0-0-27601 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| hid-uns-enc-6-1-0-0-0-0-3251 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| n320p5q2_n.apx_16 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| rbsat-v760c43649g8 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| stable-300-0.1-20-98765432130020 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x9-06068.sat.sanitized | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x9-06099.sat.sanitized | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x9-07092.sat.sanitized | SAT 2.82s | SAT 0.627s | SAT 0.627s | SAT 0.641s | **SAT 0.621s** |
| x9-10070.sat.sanitized | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
