# τ sweep on `curated_struct_eff.jsonl` (backend `eff`, timeout 120s)

## Per-τ totals

| τ | solved | timeout | mismatch | unknown | total CPU (solved) |
|---|--------|---------|----------|---------|--------------------|
| 0 | 57 | 24 | 0 | 0 | 307.5s |
| 0.5 | 55 | 26 | 0 | 0 | 244.1s |
| 1 | 54 | 27 | 0 | 0 | 223.6s |
| 2 | 54 | 27 | 0 | 0 | 230.6s |
| inf | 54 | 27 | 0 | 0 | 225.8s |

## Recommended τ

**`--eff-tau 0`** — solves **57** unique instances (wins 29 of them on fastest time; 307.5s total CPU on solved). Ranking criteria: most solved > most wins > lowest CPU.

| τ | solved | wins | CPU on solved |
|---|--------|------|---------------|
| 0 | 57 | 29 | 307.5s |
| 0.5 | 55 | 3 | 244.1s |
| 1 | 54 | 13 | 223.6s |
| 2 | 54 | 9 | 230.6s |
| inf | 54 | 3 | 225.8s |

## Best τ per family

| Family | solved | unsolved-by-any-τ | top τ (wins) |
|--------|--------|-------------------|--------------|
| (other) | 45 | 22 | 0 (27), 1 (10), 2 (4) |
| PHP | 2 | 2 | 1 (2) |
| x9/x10 | 10 | 0 | 2 (5), inf (2), 0 (2) |

## Per-problem results

| Problem | 0 | 0.5 | 1 | 2 | inf |
|---------|----------|----------|----------|----------|----------|
| 38bits_10.dimacs | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| 3col20_5_1.shuffled | UNSAT 1.3ms | UNSAT 1.3ms | **UNSAT 1.1ms** | UNSAT 1.1ms | UNSAT 1.1ms |
| 3col20_5_6.shuffled | **UNSAT 1.1ms** | UNSAT 1.5ms | UNSAT 1.1ms | UNSAT 1.1ms | UNSAT 1.1ms |
| 3col20_5_7.shuffled | UNSAT 1.3ms | UNSAT 1.6ms | **UNSAT 1.1ms** | UNSAT 1.1ms | UNSAT 1.1ms |
| 3col20_5_8.shuffled | UNSAT 1.3ms | UNSAT 1.3ms | **UNSAT 1.0ms** | UNSAT 1.0ms | UNSAT 1.0ms |
| 3col80_5_3.shuffled | **SAT 0.015s** | SAT 0.269s | SAT 0.292s | SAT 0.296s | SAT 0.304s |
| 3col80_5_5.shuffled | **SAT 0.099s** | SAT 0.112s | SAT 0.122s | SAT 0.125s | SAT 0.128s |
| 3col80_5_8.shuffled | **SAT 0.047s** | SAT 0.596s | SAT 0.775s | SAT 0.756s | SAT 0.775s |
| 40bits_10.dimacs | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| Break_04_04.xml | **SAT 0.015s** | SAT 0.242s | SAT 0.198s | SAT 0.197s | SAT 0.199s |
| Break_04_06.xml | **SAT 0.013s** | SAT 0.018s | SAT 0.016s | SAT 0.015s | SAT 0.015s |
| Break_04_08.xml | **SAT 0.014s** | SAT 0.016s | SAT 0.015s | SAT 0.014s | SAT 0.015s |
| Break_04_10.xml | SAT 0.017s | SAT 0.017s | **SAT 0.015s** | SAT 0.015s | SAT 0.015s |
| Break_triple_04_04.xml | **SAT 0.015s** | SAT 0.104s | SAT 0.088s | SAT 0.087s | SAT 0.087s |
| Break_triple_04_06.xml | **SAT 0.014s** | SAT 0.020s | SAT 0.017s | SAT 0.018s | SAT 0.018s |
| Break_triple_04_08.xml | **SAT 0.015s** | SAT 0.019s | SAT 0.016s | SAT 0.017s | SAT 0.017s |
| Break_triple_04_10.xml | SAT 0.021s | SAT 0.023s | **SAT 0.020s** | SAT 0.020s | SAT 0.021s |
| Break_unsat_04_03.xml | UNSAT 0.240s | UNSAT 0.165s | UNSAT 0.127s | UNSAT 0.129s | **UNSAT 0.126s** |
| Break_unsat_06_07.xml | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| VanDerWaerden_pd_2-3-18_298 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| VanDerWaerden_pd_2-3-18_300 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| VanDerWaerden_pd_2-3-18_311 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| VanDerWaerden_pd_2-3-18_313 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| bench_10559.smt2 | UNSAT 7.7ms | UNSAT 7.6ms | **UNSAT 7.5ms** | UNSAT 7.7ms | UNSAT 7.6ms |
| bench_11496.smt2 | UNSAT 0.038s | **UNSAT 0.036s** | UNSAT 0.037s | UNSAT 0.037s | UNSAT 0.041s |
| bench_11676.smt2 | **UNSAT 0.013s** | UNSAT 0.013s | UNSAT 0.013s | UNSAT 0.013s | UNSAT 0.013s |
| bench_14437.smt2 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| bench_1604.smt2 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| bench_16516.smt2 | UNSAT 3.6ms | **UNSAT 3.5ms** | UNSAT 3.7ms | UNSAT 3.6ms | UNSAT 3.6ms |
| bench_17124.smt2 | UNSAT 5.1ms | UNSAT 5.0ms | UNSAT 5.2ms | **UNSAT 4.9ms** | UNSAT 5.1ms |
| bench_210.smt2 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| bench_246.smt2 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| bench_5712.smt2 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| clqcolor-08-06-06.shuffled-as.sat05-1241 | **SAT 3.5ms** | SAT 3.5ms | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| ezfact16_10.shuffled | **UNSAT 0.022s** | UNSAT 2.34s | UNSAT 2.20s | UNSAT 2.26s | UNSAT 2.23s |
| ezfact16_5.shuffled | **UNSAT 0.021s** | UNSAT 1.11s | UNSAT 1.07s | UNSAT 1.07s | UNSAT 1.09s |
| ezfact16_6.shuffled | **UNSAT 0.020s** | UNSAT 32.37s | UNSAT 31.31s | UNSAT 31.23s | UNSAT 31.41s |
| ezfact16_7.shuffled | **UNSAT 0.019s** | UNSAT 0.789s | UNSAT 0.741s | UNSAT 0.753s | UNSAT 0.761s |
| ezfact16_8.shuffled | **UNSAT 0.022s** | UNSAT 0.470s | UNSAT 0.435s | UNSAT 0.429s | UNSAT 0.445s |
| ezfact32_2.shuffled | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| ezfact32_4.shuffled | **SAT 115.3s** | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| ezfact32_9.shuffled | **SAT 27.27s** | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| fclqcolor-08-06-06.shuffled-as.sat05-1265 | **SAT 2.1ms** | SAT 2.5ms | SAT 3.0ms | SAT 2.9ms | SAT 2.9ms |
| fphp-010-008.shuffled-as.sat05-1213 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| fphp-010-009.shuffled-as.sat05-1227 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| fphp-010-010.shuffled-as.sat05-1199 | SAT 1.6ms | SAT 1.6ms | SAT 1.5ms | **SAT 1.4ms** | SAT 1.4ms |
| fphp-012-012.shuffled-as.sat05-1200 | **SAT 2.1ms** | SAT 2.1ms | SAT 2.3ms | SAT 2.4ms | SAT 2.3ms |
| hcb2.shuffled-as.sat03-1430 | **UNSAT 0.5ms** | UNSAT 0.9ms | UNSAT 0.6ms | UNSAT 0.7ms | UNSAT 0.5ms |
| marg2x2.shuffled-as.sat03-1440 | UNSAT 0.7ms | UNSAT 0.7ms | UNSAT 0.7ms | **UNSAT 0.5ms** | UNSAT 0.6ms |
| marg2x3.shuffled-as.sat03-1441 | **UNSAT 5.7ms** | UNSAT 0.011s | UNSAT 6.1ms | UNSAT 6.1ms | UNSAT 6.1ms |
| mod2-rand3bip-sat-200-1.shuffled-as.sat05-2143 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| mod2-rand3bip-sat-200-2.shuffled-as.sat05-2144 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| mod2-rand3bip-sat-200-3.shuffled-as.sat05-2145 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07 | SAT 0.075s | SAT 0.077s | **SAT 0.071s** | SAT 0.072s | SAT 0.071s |
| ph12 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| ph9 | UNSAT 2.02s | UNSAT 2.08s | **UNSAT 1.95s** | UNSAT 1.99s | UNSAT 2.04s |
| php-010-008.shuffled-as.sat05-1171 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| php-010-009.shuffled-as.sat05-1185 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| php-010-010.shuffled-as.sat05-1157 | SAT 1.0ms | SAT 0.8ms | **SAT 0.7ms** | SAT 0.8ms | SAT 0.9ms |
| php-012-012.shuffled-as.sat05-1158 | SAT 1.2ms | SAT 1.2ms | **SAT 1.1ms** | SAT 1.1ms | SAT 1.2ms |
| rope_0001.shuffled | **UNSAT 0.9ms** | UNSAT 1.0ms | UNSAT 0.9ms | UNSAT 0.9ms | UNSAT 0.9ms |
| urqh1c2x2.shuffled-as.sat03-1457 | UNSAT 2.5ms | UNSAT 4.3ms | UNSAT 2.2ms | **UNSAT 2.0ms** | UNSAT 2.1ms |
| urqh1c2x3.shuffled-as.sat03-1458 | **UNSAT 22.67s** | UNSAT 47.45s | UNSAT 43.85s | UNSAT 47.29s | UNSAT 44.18s |
| urqh2x2.shuffled-as.sat03-1470 | SAT 0.8ms | SAT 0.7ms | **SAT 0.6ms** | SAT 0.7ms | SAT 0.6ms |
| x1_16.shuffled | UNSAT 0.210s | **UNSAT 0.195s** | UNSAT 0.200s | UNSAT 0.197s | UNSAT 0.203s |
| x1_24.shuffled | **UNSAT 39.25s** | UNSAT 46.65s | UNSAT 41.74s | UNSAT 44.04s | UNSAT 42.22s |
| x1_32.shuffled | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| x1_36.shuffled-as.sat03-1589 | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| x2_16.shuffled | **UNSAT 0.253s** | UNSAT 0.274s | UNSAT 0.254s | UNSAT 0.263s | UNSAT 0.265s |
| x2_24.shuffled | UNSAT 99.6s | UNSAT 108.5s | **UNSAT 98.0s** | UNSAT 99.1s | UNSAT 99.0s |
| x2_32.shuffled | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s | TIMEOUT 120.0s |
| x9-02007.sat.sanitized | SAT 4.1ms | SAT 2.0ms | **SAT 1.5ms** | SAT 1.6ms | SAT 1.6ms |
| x9-02021.sat.sanitized | UNSAT 9.3ms | UNSAT 6.4ms | UNSAT 5.6ms | UNSAT 5.7ms | **UNSAT 5.5ms** |
| x9-02023.sat.sanitized | **SAT 5.0ms** | SAT 6.8ms | SAT 5.4ms | SAT 5.1ms | SAT 5.0ms |
| x9-02036.sat.sanitized | UNSAT 0.011s | UNSAT 7.2ms | UNSAT 6.2ms | **UNSAT 6.0ms** | UNSAT 6.1ms |
| x9-02042.sat.sanitized | UNSAT 0.016s | UNSAT 8.4ms | UNSAT 7.7ms | **UNSAT 7.5ms** | UNSAT 7.6ms |
| x9-02043.sat.sanitized | SAT 3.9ms | SAT 2.1ms | SAT 1.6ms | **SAT 1.5ms** | SAT 1.6ms |
| x9-02044.sat.sanitized | **SAT 2.0ms** | SAT 3.6ms | SAT 3.3ms | SAT 3.3ms | SAT 3.3ms |
| x9-02053.sat.sanitized | UNSAT 0.018s | UNSAT 9.7ms | UNSAT 9.0ms | **UNSAT 8.7ms** | UNSAT 8.8ms |
| x9-02073.sat.sanitized | UNSAT 0.014s | UNSAT 8.1ms | UNSAT 7.3ms | UNSAT 7.2ms | **UNSAT 7.1ms** |
| x9-02090.sat.sanitized | SAT 9.6ms | SAT 6.0ms | SAT 5.2ms | **SAT 5.1ms** | SAT 5.1ms |
