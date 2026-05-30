# τ sweep on `curated_struct_eff.jsonl` (backend `eff`, timeout 60s)

## Per-τ totals

| τ | solved | timeout | mismatch | unknown | total CPU (solved) |
|---|--------|---------|----------|---------|--------------------|
| 0 | 55 | 26 | 0 | 0 | 96.7s |
| 0.5 | 54 | 27 | 0 | 0 | 133.5s |
| 1 | 53 | 28 | 0 | 0 | 131.6s |
| 2 | 53 | 28 | 0 | 0 | 128.3s |
| inf | 53 | 28 | 0 | 0 | 132.5s |

## Recommended τ

**`--eff-tau 0`** — solves **55** unique instances (wins 24 of them on fastest time; 96.7s total CPU on solved). Ranking criteria: most solved > most wins > lowest CPU.

| τ | solved | wins | CPU on solved |
|---|--------|------|---------------|
| 0 | 55 | 24 | 96.7s |
| 0.5 | 54 | 6 | 133.5s |
| 1 | 53 | 11 | 131.6s |
| 2 | 53 | 9 | 128.3s |
| inf | 53 | 5 | 132.5s |

## Best τ per family

| Family | solved | unsolved-by-any-τ | top τ (wins) |
|--------|--------|-------------------|--------------|
| (other) | 43 | 24 | 0 (22), 1 (7), 2 (6) |
| PHP | 2 | 2 | 0 (1), 0.5 (1) |
| x9/x10 | 10 | 0 | 1 (4), 2 (3), inf (2) |

## Per-problem results

| Problem | 0 | 0.5 | 1 | 2 | inf |
|---------|----------|----------|----------|----------|----------|
| 38bits_10.dimacs | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 3col20_5_1.shuffled | UNSAT 1.6ms | UNSAT 1.4ms | **UNSAT 1.1ms** | UNSAT 1.1ms | UNSAT 1.2ms |
| 3col20_5_6.shuffled | UNSAT 1.2ms | UNSAT 1.9ms | UNSAT 1.2ms | UNSAT 1.2ms | **UNSAT 1.1ms** |
| 3col20_5_7.shuffled | UNSAT 1.9ms | UNSAT 1.5ms | **UNSAT 1.1ms** | UNSAT 1.2ms | UNSAT 1.2ms |
| 3col20_5_8.shuffled | UNSAT 1.5ms | UNSAT 1.5ms | **UNSAT 1.0ms** | UNSAT 1.0ms | UNSAT 1.0ms |
| 3col80_5_3.shuffled | **SAT 0.019s** | SAT 0.369s | SAT 0.415s | SAT 0.411s | SAT 0.455s |
| 3col80_5_5.shuffled | **SAT 0.104s** | SAT 0.143s | SAT 0.157s | SAT 0.152s | SAT 0.170s |
| 3col80_5_8.shuffled | **SAT 0.054s** | SAT 0.688s | SAT 0.827s | SAT 0.888s | SAT 1.09s |
| 40bits_10.dimacs | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| Break_04_04.xml | **SAT 0.017s** | SAT 0.236s | SAT 0.209s | SAT 0.212s | SAT 0.216s |
| Break_04_06.xml | **SAT 0.017s** | SAT 0.019s | SAT 0.017s | SAT 0.018s | SAT 0.018s |
| Break_04_08.xml | SAT 0.018s | SAT 0.017s | **SAT 0.015s** | SAT 0.015s | SAT 0.015s |
| Break_04_10.xml | SAT 0.020s | SAT 0.018s | **SAT 0.016s** | SAT 0.016s | SAT 0.017s |
| Break_triple_04_04.xml | **SAT 0.017s** | SAT 0.106s | SAT 0.096s | SAT 0.098s | SAT 0.096s |
| Break_triple_04_06.xml | **SAT 0.016s** | SAT 0.021s | SAT 0.019s | SAT 0.018s | SAT 0.021s |
| Break_triple_04_08.xml | **SAT 0.016s** | SAT 0.019s | SAT 0.018s | SAT 0.018s | SAT 0.018s |
| Break_triple_04_10.xml | SAT 0.032s | SAT 0.024s | SAT 0.022s | **SAT 0.021s** | SAT 0.022s |
| Break_unsat_04_03.xml | UNSAT 0.277s | UNSAT 0.163s | **UNSAT 0.134s** | UNSAT 0.137s | UNSAT 0.137s |
| Break_unsat_06_07.xml | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_298 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_300 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_311 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_313 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_10559.smt2 | **UNSAT 7.7ms** | UNSAT 8.2ms | UNSAT 8.0ms | UNSAT 8.2ms | UNSAT 8.1ms |
| bench_11496.smt2 | UNSAT 0.040s | UNSAT 0.038s | **UNSAT 0.036s** | UNSAT 0.039s | UNSAT 0.039s |
| bench_11676.smt2 | **UNSAT 0.013s** | UNSAT 0.015s | UNSAT 0.014s | UNSAT 0.013s | UNSAT 0.015s |
| bench_14437.smt2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_1604.smt2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_16516.smt2 | UNSAT 3.9ms | UNSAT 3.9ms | UNSAT 3.7ms | **UNSAT 3.6ms** | UNSAT 3.7ms |
| bench_17124.smt2 | UNSAT 5.1ms | UNSAT 5.3ms | UNSAT 5.0ms | **UNSAT 4.9ms** | UNSAT 4.9ms |
| bench_210.smt2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_246.smt2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_5712.smt2 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| clqcolor-08-06-06.shuffled-as.sat05-1241 | **SAT 4.6ms** | SAT 5.1ms | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| ezfact16_10.shuffled | **UNSAT 0.023s** | UNSAT 2.86s | UNSAT 2.89s | UNSAT 2.86s | UNSAT 2.96s |
| ezfact16_5.shuffled | **UNSAT 0.021s** | UNSAT 1.61s | UNSAT 1.56s | UNSAT 1.59s | UNSAT 1.64s |
| ezfact16_6.shuffled | **UNSAT 0.021s** | UNSAT 40.04s | UNSAT 39.06s | UNSAT 38.61s | UNSAT 38.90s |
| ezfact16_7.shuffled | **UNSAT 0.020s** | UNSAT 0.968s | UNSAT 0.946s | UNSAT 0.960s | UNSAT 1.01s |
| ezfact16_8.shuffled | **UNSAT 0.023s** | UNSAT 0.596s | UNSAT 0.613s | UNSAT 0.643s | UNSAT 0.614s |
| ezfact32_2.shuffled | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| ezfact32_4.shuffled | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| ezfact32_9.shuffled | **SAT 27.94s** | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| fclqcolor-08-06-06.shuffled-as.sat05-1265 | SAT 3.6ms | **SAT 3.2ms** | SAT 4.4ms | SAT 5.4ms | SAT 4.4ms |
| fphp-010-008.shuffled-as.sat05-1213 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| fphp-010-009.shuffled-as.sat05-1227 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| fphp-010-010.shuffled-as.sat05-1199 | SAT 2.1ms | SAT 2.1ms | SAT 1.9ms | **SAT 1.8ms** | SAT 2.2ms |
| fphp-012-012.shuffled-as.sat05-1200 | **SAT 3.4ms** | SAT 3.4ms | SAT 3.5ms | SAT 3.9ms | SAT 3.5ms |
| hcb2.shuffled-as.sat03-1430 | **UNSAT 0.7ms** | UNSAT 0.7ms | UNSAT 0.8ms | UNSAT 0.9ms | UNSAT 0.7ms |
| marg2x2.shuffled-as.sat03-1440 | UNSAT 0.8ms | **UNSAT 0.6ms** | UNSAT 0.8ms | UNSAT 0.7ms | UNSAT 0.6ms |
| marg2x3.shuffled-as.sat03-1441 | **UNSAT 6.1ms** | UNSAT 6.6ms | UNSAT 6.2ms | UNSAT 6.2ms | UNSAT 6.6ms |
| mod2-rand3bip-sat-200-1.shuffled-as.sat05-2143 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| mod2-rand3bip-sat-200-2.shuffled-as.sat05-2144 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| mod2-rand3bip-sat-200-3.shuffled-as.sat05-2145 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07 | SAT 0.086s | SAT 0.084s | SAT 0.083s | SAT 0.086s | **SAT 0.082s** |
| ph12 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| ph9 | UNSAT 2.09s | **UNSAT 1.93s** | UNSAT 1.96s | UNSAT 2.02s | UNSAT 2.03s |
| php-010-008.shuffled-as.sat05-1171 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| php-010-009.shuffled-as.sat05-1185 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| php-010-010.shuffled-as.sat05-1157 | **SAT 0.9ms** | SAT 0.9ms | SAT 0.9ms | SAT 0.9ms | SAT 0.9ms |
| php-012-012.shuffled-as.sat05-1158 | SAT 1.6ms | **SAT 1.4ms** | SAT 1.5ms | SAT 1.5ms | SAT 1.8ms |
| rope_0001.shuffled | UNSAT 1.2ms | UNSAT 1.1ms | UNSAT 1.2ms | **UNSAT 1.0ms** | UNSAT 1.5ms |
| urqh1c2x2.shuffled-as.sat03-1457 | UNSAT 2.8ms | UNSAT 2.6ms | UNSAT 2.2ms | **UNSAT 2.1ms** | UNSAT 2.3ms |
| urqh1c2x3.shuffled-as.sat03-1458 | **UNSAT 23.59s** | UNSAT 47.22s | UNSAT 44.84s | UNSAT 42.48s | UNSAT 45.92s |
| urqh2x2.shuffled-as.sat03-1470 | **SAT 0.6ms** | SAT 0.7ms | SAT 0.7ms | SAT 0.6ms | SAT 0.6ms |
| x1_16.shuffled | UNSAT 0.212s | **UNSAT 0.188s** | UNSAT 0.196s | UNSAT 0.198s | UNSAT 0.195s |
| x1_24.shuffled | UNSAT 41.56s | **UNSAT 35.81s** | UNSAT 37.08s | UNSAT 36.48s | UNSAT 36.47s |
| x1_32.shuffled | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x1_36.shuffled-as.sat03-1589 | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x2_16.shuffled | UNSAT 0.265s | UNSAT 0.253s | UNSAT 0.258s | UNSAT 0.258s | **UNSAT 0.251s** |
| x2_24.shuffled | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x2_32.shuffled | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x9-02007.sat.sanitized | SAT 5.1ms | SAT 2.2ms | SAT 2.1ms | SAT 2.1ms | **SAT 2.0ms** |
| x9-02021.sat.sanitized | UNSAT 0.013s | UNSAT 6.7ms | **UNSAT 5.8ms** | UNSAT 6.5ms | UNSAT 6.0ms |
| x9-02023.sat.sanitized | SAT 6.3ms | SAT 8.1ms | **SAT 5.8ms** | SAT 6.1ms | SAT 5.8ms |
| x9-02036.sat.sanitized | UNSAT 0.014s | UNSAT 7.3ms | UNSAT 6.7ms | **UNSAT 6.4ms** | UNSAT 6.6ms |
| x9-02042.sat.sanitized | UNSAT 0.018s | UNSAT 9.0ms | **UNSAT 7.9ms** | UNSAT 7.9ms | UNSAT 8.0ms |
| x9-02043.sat.sanitized | SAT 5.1ms | SAT 2.2ms | SAT 2.0ms | **SAT 1.9ms** | SAT 2.0ms |
| x9-02044.sat.sanitized | **SAT 2.3ms** | SAT 4.4ms | SAT 4.1ms | SAT 3.8ms | SAT 3.7ms |
| x9-02053.sat.sanitized | UNSAT 0.021s | UNSAT 0.010s | **UNSAT 9.2ms** | UNSAT 9.2ms | UNSAT 9.2ms |
| x9-02073.sat.sanitized | UNSAT 0.017s | UNSAT 8.7ms | UNSAT 7.9ms | UNSAT 7.9ms | **UNSAT 7.6ms** |
| x9-02090.sat.sanitized | SAT 0.013s | SAT 6.5ms | SAT 6.3ms | **SAT 5.8ms** | SAT 5.9ms |
