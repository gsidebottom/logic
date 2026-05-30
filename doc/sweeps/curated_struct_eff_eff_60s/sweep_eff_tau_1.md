# Competition Benchmark Results (index=curated_struct_eff.jsonl, timeout=60s, backend=eff, parallel=10)

## Summary

| Result | Count | % |
|--------|-------|---|
| SAT | 23 | 28.4% |
| UNSAT | 30 | 37.0% |
| TIMEOUT | 28 | 34.6% |
| **Total** | 81 | 100% |

### Solver effort (mean (min-max))

| Group | N | Paths covered | Conflicts | Conf/s | Restarts | Rst/s |
|-------|---|---------------|-----------|--------|----------|-------|
| SAT | 23 | 45.6% (0.0%-100.0%) | 397 (0-4.8K) | 14.3K (0-58.1K) | 2 (0-25) | 87 (0-345) |
| UNSAT | 30 | 95.6% (90.7%-100.0%) | 216 (30-698) | 65.0K (28.3K-125.9K) | 1 (0-5) | 345 (0-909) |
| TIMEOUT | 28 | 31.4% (0.0%-100.0%) | 470.4K (29.2K-1.6M) | 7.8K (487-26.7K) | 977 (107-3.1K) | 16 (2-52) |
| Total | 81 | 50.6% (0.0%-100.0%) | 216.1K (0-1.6M) | 22.9K (0-125.9K) | 450 (0-3.1K) | 114 (0-909) |

## Cactus plot

![cactus plot](sweep_eff_tau_1.png)

## Per-problem results

| Problem | Result | Time | Paths | Total | Conf | Rst |
|---------|--------|------|-------|-------|------|-----|
| bench_16516.smt2 | UNSAT | 0.0037s | — | — | — | — |
| php-010-010.shuffled-as.sat05-1157 | SAT | 0.0009s | 2.91e+145 | 10^145.5 | 0 | 0 |
| bench_10559.smt2 | UNSAT | 0.008s | — | — | — | — |
| bench_17124.smt2 | UNSAT | 0.005s | — | — | — | — |
| bench_11676.smt2 | UNSAT | 0.0143s | — | — | — | — |
| fphp-010-010.shuffled-as.sat05-1199 | SAT | 0.0019s | 8.45e+280 | 10^280.9 | 5 | 0 |
| fphp-012-012.shuffled-as.sat05-1200 | SAT | 0.0035s | 1 | 10^489.8 | 5 | 0 |
| php-012-012.shuffled-as.sat05-1158 | SAT | 0.0015s | 2.32e+251 | 10^251.4 | 0 | 0 |
| urqh2x2.shuffled-as.sat03-1470 | SAT | 0.0007s | 2.00e+63 | 10^63.3 | 21 | 0 |
| marg2x2.shuffled-as.sat03-1440 | UNSAT | 0.0008s | 1.9P | 10^15.3 | 30 | 0 |
| bench_11496.smt2 | UNSAT | 0.0365s | — | — | — | — |
| hcb2.shuffled-as.sat03-1430 | UNSAT | 0.0008s | 1.9P | 10^15.3 | 30 | 0 |
| urqh1c2x2.shuffled-as.sat03-1457 | UNSAT | 0.0022s | 4.30e+39 | 10^39.6 | 277 | 2 |
| marg2x3.shuffled-as.sat03-1441 | UNSAT | 0.0062s | 1.49e+40 | 10^40.2 | 698 | 5 |
| fclqcolor-08-06-06.shuffled-as.sat05-1265 | SAT | 0.0044s | 1 | 10^615.4 | 36 | 0 |
| mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07 | SAT | 0.0826s | 1 | 10^336.6 | 4.8K | 25 |
| urqh1c2x3.shuffled-as.sat03-1458 | UNSAT | 44.8439s | — | — | — | — |
| 3col80_5_8.shuffled | SAT | 0.827s | — | — | — | — |
| 3col80_5_5.shuffled | SAT | 0.1569s | — | — | — | — |
| rope_0001.shuffled | UNSAT | 0.0012s | 2.51e+27 | 10^27.4 | 34 | 0 |
| 3col80_5_3.shuffled | SAT | 0.4147s | — | — | — | — |
| bench_5712.smt2 | TIMEOUT | 60s | 0 | 10^438.9 | 1.6M | 3.1K |
| bench_14437.smt2 | TIMEOUT | 60s | 0 | 10^515.7 | 1.2M | 2.3K |
| bench_210.smt2 | TIMEOUT | 60s | 0 | 10^480.5 | 1.5M | 2.8K |
| bench_246.smt2 | TIMEOUT | 60s | 0 | 10^558.9 | 1.5M | 3.0K |
| bench_1604.smt2 | TIMEOUT | 60s | 0 | 10^513.2 | 1.5M | 2.9K |
| mod2-rand3bip-sat-200-3.shuffled-as.sat05-2145 | TIMEOUT | 60s | 0 | 10^381.7 | 71.4K | 220 |
| ph12 | TIMEOUT | 60s | 3.11e+295 | 10^295.5 | 63.1K | 189 |
| fphp-010-008.shuffled-as.sat05-1213 | TIMEOUT | 60s | 4.90e+201 | 10^201.7 | 63.9K | 189 |
| clqcolor-08-06-06.shuffled-as.sat05-1241 | TIMEOUT | 60s | 0 | 10^528.7 | 100.2K | 254 |
| 3col20_5_8.shuffled | UNSAT | 0.001s | 2.89e+76 | 10^76.5 | 79 | 0 |
| 3col20_5_7.shuffled | UNSAT | 0.0011s | 2.89e+76 | 10^76.5 | 113 | 1 |
| 3col20_5_1.shuffled | UNSAT | 0.0011s | 2.89e+76 | 10^76.5 | 91 | 0 |
| 3col20_5_6.shuffled | UNSAT | 0.0012s | 2.89e+76 | 10^76.5 | 115 | 1 |
| Break_04_06.xml | SAT | 0.0168s | 1 | 10^390.8 | 120 | 1 |
| Break_04_08.xml | SAT | 0.0152s | 1 | 10^400.7 | 128 | 1 |
| Break_triple_04_06.xml | SAT | 0.0186s | 1 | 10^400.9 | 134 | 1 |
| Break_triple_04_08.xml | SAT | 0.0175s | 1 | 10^410.7 | 103 | 1 |
| Break_04_10.xml | SAT | 0.016s | 1 | 10^399.7 | 110 | 1 |
| x9-02007.sat.sanitized | SAT | 0.0021s | 1.88e+301 | 10^301.3 | 15 | 0 |
| x9-02023.sat.sanitized | SAT | 0.0058s | 4.91e+302 | 10^302.7 | 205 | 2 |
| x9-02044.sat.sanitized | SAT | 0.0041s | 3.61e+301 | 10^301.6 | 135 | 1 |
| Break_triple_04_10.xml | SAT | 0.0224s | 1 | 10^409.7 | 104 | 1 |
| x9-02090.sat.sanitized | SAT | 0.0063s | 6.93e+301 | 10^301.8 | 216 | 2 |
| x9-02043.sat.sanitized | SAT | 0.002s | 1.33e+302 | 10^302.1 | 12 | 0 |
| x9-02036.sat.sanitized | UNSAT | 0.0067s | 3.61e+301 | 10^301.6 | 282 | 2 |
| x9-02042.sat.sanitized | UNSAT | 0.0079s | 6.93e+301 | 10^301.8 | 325 | 2 |
| x9-02021.sat.sanitized | UNSAT | 0.0058s | 4.91e+302 | 10^302.7 | 239 | 2 |
| x9-02053.sat.sanitized | UNSAT | 0.0092s | 2.56e+302 | 10^302.4 | 398 | 2 |
| x9-02073.sat.sanitized | UNSAT | 0.0079s | 6.93e+301 | 10^301.8 | 313 | 2 |
| Break_triple_04_04.xml | SAT | 0.096s | 1 | 10^388.1 | 1.4K | 9 |
| Break_unsat_04_03.xml | UNSAT | 0.1335s | — | — | — | — |
| Break_04_04.xml | SAT | 0.2093s | — | — | — | — |
| ezfact16_8.shuffled | UNSAT | 0.6126s | — | — | — | — |
| ezfact16_7.shuffled | UNSAT | 0.9459s | — | — | — | — |
| ezfact16_5.shuffled | UNSAT | 1.5613s | — | — | — | — |
| ph9 | UNSAT | 1.955s | — | — | — | — |
| ezfact16_10.shuffled | UNSAT | 2.8857s | — | — | — | — |
| x1_16.shuffled | UNSAT | 0.1961s | — | — | — | — |
| x2_16.shuffled | UNSAT | 0.2579s | — | — | — | — |
| ezfact16_6.shuffled | UNSAT | 39.0622s | — | — | — | — |
| php-010-008.shuffled-as.sat05-1171 | TIMEOUT | 60s | 2.52e+117 | 10^117.4 | 68.9K | 216 |
| Break_unsat_06_07.xml | TIMEOUT | 60s | 0 | 10^1677.0 | 33.6K | 123 |
| ezfact32_9.shuffled | TIMEOUT | 60s | 0 | 10^2640.3 | 1.5M | 3.0K |
| ezfact32_2.shuffled | TIMEOUT | 60s | 0 | 10^2640.3 | 1.4M | 2.8K |
| ezfact32_4.shuffled | TIMEOUT | 60s | 0 | 10^2640.3 | 1.3M | 2.6K |
| fphp-010-009.shuffled-as.sat05-1227 | TIMEOUT | 60s | 6.77e+239 | 10^239.8 | 55.6K | 172 |
| mod2-rand3bip-sat-200-2.shuffled-as.sat05-2144 | TIMEOUT | 60s | 0 | 10^381.7 | 79.7K | 251 |
| php-010-009.shuffled-as.sat05-1185 | TIMEOUT | 60s | 2.88e+131 | 10^131.5 | 64.0K | 190 |
| VanDerWaerden_pd_2-3-18_311 | TIMEOUT | 60s | 0 | 10^7092.6 | 30.9K | 113 |
| x1_24.shuffled | UNSAT | 37.0821s | — | — | — | — |
| x2_24.shuffled | TIMEOUT | 60s | 9.40e+83 | 10^84.0 | 127.1K | 346 |
| x2_32.shuffled | TIMEOUT | 60s | 2.12e+118 | 10^118.3 | 131.5K | 361 |
| x1_32.shuffled | TIMEOUT | 60s | 2.12e+118 | 10^118.3 | 130.4K | 355 |
| VanDerWaerden_pd_2-3-18_313 | TIMEOUT | 60s | 0 | 10^7184.5 | 29.4K | 107 |
| 38bits_10.dimacs | TIMEOUT | 60s | 0 | 10^10614.9 | 184.1K | 507 |
| 40bits_10.dimacs | TIMEOUT | 60s | 0 | 10^10877.8 | 175.6K | 483 |
| mod2-rand3bip-sat-200-1.shuffled-as.sat05-2143 | TIMEOUT | 60s | 0 | 10^381.7 | 73.0K | 227 |
| VanDerWaerden_pd_2-3-18_300 | TIMEOUT | 60s | 0 | 10^6746.6 | 29.2K | 107 |
| VanDerWaerden_pd_2-3-18_298 | TIMEOUT | 60s | 0 | 10^6655.4 | 30.2K | 108 |
| x1_36.shuffled-as.sat03-1589 | TIMEOUT | 60s | 3.93e+133 | 10^133.6 | 129.5K | 348 |
