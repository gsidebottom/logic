# τ sweep on `curated_struct_eff.jsonl` (backend `eff`, timeout 60s)

## Per-τ totals

| τ | solved | timeout | mismatch | unknown | total CPU (solved) |
|---|--------|---------|----------|---------|--------------------|
| 0 | 21 | 0 | 0 | 1 | 0.3s |
| 0.5 | 53 | 18 | 0 | 1 | 89.2s |
| 1 | 53 | 28 | 0 | 0 | 126.9s |
| 2 | 53 | 28 | 0 | 0 | 122.8s |
| inf | 53 | 28 | 0 | 0 | 126.7s |

## Recommended τ

**`--eff-tau 0.5`** — solves **53** unique instances (wins 53 of them on fastest time; 89.2s total CPU on solved). Ranking criteria: most solved > most wins > lowest CPU.

| τ | solved | wins | CPU on solved |
|---|--------|------|---------------|
| 0.5 | 53 | 53 | 89.2s |
| inf | 53 | 17 | 126.7s |
| 2 | 53 | 14 | 122.8s |
| 1 | 53 | 10 | 126.9s |
| 0 | 21 | 13 | 0.3s |

## Best τ per family

| Family | solved | unsolved-by-any-τ | top τ (wins) |
|--------|--------|-------------------|--------------|
| (other) | 95 | 44 | 0.5 (53), inf (13), 0 (13) |
| PHP | 2 | 2 | 2 (1), 1 (1) |
| x9/x10 | 10 | 0 | 1 (4), inf (4), 2 (2) |

## Per-problem results

| Problem | 0 | 0.5 | 1 | 2 | inf |
|---------|----------|----------|----------|----------|----------|
| 00f969737ba4338bd233cd3ed249bd55 | — | **UNSAT 1.3ms** | — | — | — |
| 04e47e6635908600ef3938b32644825a | — | **UNSAT 2.0ms** | — | — | — |
| 067dc6945c4aec1c2bc1fdc2e5819124 | — | **UNSAT 1.7ms** | — | — | — |
| 076d4d6f83306ee69c35e3c99e30d8f8 | — | **UNSAT 0.266s** | — | — | — |
| 081f111af59344b61346367a930e24f6 | — | **SAT 0.022s** | — | — | — |
| 09d7add3bf3b75c5d1023a92e752989a | — | **UNSAT 0.186s** | — | — | — |
| 0b3d82edadec4016376020c779b7ee96 | — | TIMEOUT 60.0s | — | — | — |
| 0f511f22d013d6559dff68fbd2cf2a6b | — | TIMEOUT 60.0s | — | — | — |
| 196673fd5fd26eebd8a9a2639a5f8228 | — | **SAT 0.026s** | — | — | — |
| 1b073533cf08d6cbb3d40187b9529015 | — | TIMEOUT 60.0s | — | — | — |
| 1cf67760092ebabc1bb42706fb8d43dc | — | **SAT 0.7ms** | — | — | — |
| 1eabc0df9be862042637dbb555212a21 | — | TIMEOUT 60.0s | — | — | — |
| 22a7132d84d753d8702475e8ced552e3 | — | TIMEOUT 60.0s | — | — | — |
| 2852ff304840ef05f74484839c68af5a | — | **SAT 0.022s** | — | — | — |
| 2b22fa650cb144ab070df446d32c1b7a | — | **SAT 0.019s** | — | — | — |
| 2b738a1991a7318cad993a809b10cc2c | — | **UNSAT 1.2ms** | — | — | — |
| 2b8b0161c772b1470b0a754b8c93ccc0 | — | **SAT 0.118s** | — | — | — |
| 38bits_10.dimacs | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 3c917e77148a8f645a60d28d8fb53fe8 | — | **UNSAT 3.5ms** | — | — | — |
| 3col20_5_1.shuffled | — | — | UNSAT 1.1ms | UNSAT 1.1ms | **UNSAT 1.0ms** |
| 3col20_5_6.shuffled | — | — | **UNSAT 1.1ms** | UNSAT 1.1ms | UNSAT 1.2ms |
| 3col20_5_7.shuffled | — | — | **UNSAT 1.1ms** | UNSAT 1.1ms | UNSAT 1.2ms |
| 3col20_5_8.shuffled | — | — | **UNSAT 1.0ms** | UNSAT 1.0ms | UNSAT 1.0ms |
| 3col80_5_3.shuffled | **SAT 0.015s** | — | SAT 0.339s | SAT 0.302s | SAT 0.307s |
| 3col80_5_5.shuffled | **SAT 0.098s** | — | SAT 0.133s | SAT 0.133s | SAT 0.125s |
| 3col80_5_8.shuffled | **SAT 0.049s** | — | SAT 0.824s | SAT 0.809s | SAT 0.822s |
| 40bits_10.dimacs | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| 44092fcc83a5cba81419e82cfd18602c | — | TIMEOUT 60.0s | — | — | — |
| 44ab80d376f78495483e45bb8088c3ae | — | TIMEOUT 60.0s | — | — | — |
| 44b54e58f765fc6287f73da16d3455b6 | — | **UNSAT 9.4ms** | — | — | — |
| 450def045f49aea7022fae69bc684da9 | — | **UNSAT 8.5ms** | — | — | — |
| 4f968e0bb4a9609933e006ebc53a27ef | — | **UNSAT 1.6ms** | — | — | — |
| 50a6d53dfb7c3f6de126290275f800b9 | — | TIMEOUT 60.0s | — | — | — |
| 50e676c0054780a447f7c5d0c8f18e12 | — | **SAT 6.5ms** | — | — | — |
| 548e52cb4ef6625e0eef3f969b2afbd6 | — | TIMEOUT 60.0s | — | — | — |
| 55c0dbf680e0ab5c6263feb4ad143c0e | — | **UNSAT 2.58s** | — | — | — |
| 5d4085fbec7001434c266a85694feb21 | — | **UNSAT 0.013s** | — | — | — |
| 5db39e5a8ccde4e52c13a10cd2cc5c13 | — | **SAT 5.9ms** | — | — | — |
| 6267db146493cddb49bd4adcdf634d75 | — | **UNSAT 5.0ms** | — | — | — |
| 68eb522c6e1666736ff302a943cf722d | — | **SAT 1.3ms** | — | — | — |
| 691c3a7092c55987d9a6e973e8ffda6d | — | **SAT 2.1ms** | — | — | — |
| 69f6dd335626a9b71bfc6f2332f52b9d | — | **SAT 0.230s** | — | — | — |
| 6b36abc94899ab1d25a9c48d7697916c | — | **UNSAT 0.9ms** | — | — | — |
| 6ff98b815c0ff57d92086702e7dd2829 | — | **UNSAT 2.5ms** | — | — | — |
| 7894494e310c19322a7627adfd57f941 | — | **UNSAT 2.06s** | — | — | — |
| 7f7109dce621ef361a72b3e8cee9a962 | — | TIMEOUT 60.0s | — | — | — |
| 8188f17216adc523f5f5c46770c9b923 | — | **SAT 0.641s** | — | — | — |
| 81fe63cbee3d00cdb5edd8d48dd9c194 | — | **SAT 3.5ms** | — | — | — |
| 8297543bf1983c01b627fcb73f7edb86 | — | **UNSAT 7.8ms** | — | — | — |
| 87078e29f06cb461491342524817903c | — | TIMEOUT 60.0s | — | — | — |
| 8e4c0c8287ae05d071c3ccb9fc58f514 | — | **UNSAT 6.5ms** | — | — | — |
| 90d2c6c480c80c39d0e8005bd405ecd4 | — | TIMEOUT 60.0s | — | — | — |
| 9440117095ba6242e74dd55a5d0022ba | — | **UNSAT 0.011s** | — | — | — |
| 97f0882d3c8f1d17c100c1b3214c00e7 | — | **SAT 0.101s** | — | — | — |
| 9dbc810fad5521ab521f47d6b2c445e9 | — | **UNSAT 32.37s** | — | — | — |
| Break_04_04.xml | — | — | SAT 0.209s | **SAT 0.198s** | SAT 0.203s |
| Break_04_06.xml | — | — | SAT 0.016s | SAT 0.016s | **SAT 0.016s** |
| Break_04_08.xml | — | — | SAT 0.015s | SAT 0.014s | **SAT 0.014s** |
| Break_04_10.xml | — | — | SAT 0.015s | **SAT 0.015s** | SAT 0.015s |
| Break_triple_04_04.xml | — | — | SAT 0.090s | SAT 0.087s | **SAT 0.087s** |
| Break_triple_04_06.xml | — | — | SAT 0.018s | SAT 0.018s | **SAT 0.017s** |
| Break_triple_04_08.xml | — | — | SAT 0.018s | **SAT 0.017s** | SAT 0.017s |
| Break_triple_04_10.xml | — | — | SAT 0.021s | SAT 0.021s | **SAT 0.020s** |
| Break_unsat_04_03.xml | — | — | UNSAT 0.131s | **UNSAT 0.124s** | UNSAT 0.131s |
| Break_unsat_06_07.xml | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_298 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_300 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_311 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| VanDerWaerden_pd_2-3-18_313 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| a2a1e9115052e386dc635fdfabcfee04 | — | TIMEOUT 60.0s | — | — | — |
| a53f5bdf5c68f006c146f172fdd5a49d | — | **UNSAT 1.1ms** | — | — | — |
| a8197b18e7e2e2edc6b8deaa0a72e7c3 | — | **UNSAT 1.20s** | — | — | — |
| ab6226668c0f445cc9a291776d70ac93 | — | **UNSAT 0.037s** | — | — | — |
| affed3d1f6340f16ddd6b833a2d1e59a | — | UNKNOWN | — | — | — |
| b94b22c47464dd91afb00167a39c6624 | — | **SAT 0.270s** | — | — | — |
| bench_10559.smt2 | **UNSAT 7.6ms** | — | UNSAT 7.9ms | UNSAT 7.8ms | UNSAT 8.0ms |
| bench_11496.smt2 | **UNSAT 0.036s** | — | UNSAT 0.037s | UNSAT 0.038s | UNSAT 0.037s |
| bench_11676.smt2 | UNSAT 0.014s | — | UNSAT 0.014s | **UNSAT 0.013s** | UNSAT 0.013s |
| bench_14437.smt2 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_1604.smt2 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_16516.smt2 | **UNSAT 3.6ms** | — | UNSAT 3.6ms | UNSAT 3.6ms | UNSAT 3.6ms |
| bench_17124.smt2 | UNSAT 4.9ms | — | UNSAT 5.0ms | UNSAT 5.0ms | **UNSAT 4.8ms** |
| bench_210.smt2 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_246.smt2 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bench_5712.smt2 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| bf04d71a5934d6bea43dce9b9e634fb0 | — | TIMEOUT 60.0s | — | — | — |
| bf6ed42209c6d0feedccfa1c519890ea | — | **SAT 2.8ms** | — | — | — |
| c4140f359ede42a52576a8d969b927bb | — | **SAT 7.3ms** | — | — | — |
| c494b37baac19c2c40eafe642fb142b1 | — | **UNSAT 0.482s** | — | — | — |
| c589cd14f61278a0c0e507dde649704f | — | **SAT 0.030s** | — | — | — |
| c66167837eaad5a6ddc6ee40fa77488f | — | **SAT 2.1ms** | — | — | — |
| c7d10eee6ce5f663697f3146ec866c69 | — | **UNSAT 47.23s** | — | — | — |
| cb907723735deac3c664753c4be24c77 | — | TIMEOUT 60.0s | — | — | — |
| clqcolor-08-06-06.shuffled-as.sat05-1241 | **SAT 3.4ms** | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| d2b4a9ea1313121cf1c9c7f420028aea | — | **SAT 2.3ms** | — | — | — |
| d497dfe93d877c9488e8fd1fdec40c73 | — | **SAT 0.040s** | — | — | — |
| d6fc8244dafa817cb8f8b100df8ae288 | — | **SAT 0.9ms** | — | — | — |
| da1c4b80744ff527a61cafd64d069897 | — | **SAT 1.6ms** | — | — | — |
| daa64046112eb50107587b859f856a7d | — | TIMEOUT 60.0s | — | — | — |
| dda1ea51d1cda9027522c7097c889a64 | — | **UNSAT 7.6ms** | — | — | — |
| e8fe33f0783b5108cad8f94a0a122df0 | — | TIMEOUT 60.0s | — | — | — |
| e9f92272ae6a21a0448ce9bcf6187256 | — | **UNSAT 0.890s** | — | — | — |
| ee69be884f3afc678a0e410b8c5976fc | — | TIMEOUT 60.0s | — | — | — |
| ezfact16_10.shuffled | — | — | UNSAT 2.36s | **UNSAT 2.28s** | UNSAT 2.29s |
| ezfact16_5.shuffled | — | — | UNSAT 1.08s | UNSAT 1.10s | **UNSAT 1.05s** |
| ezfact16_6.shuffled | — | — | UNSAT 31.42s | **UNSAT 30.93s** | UNSAT 31.42s |
| ezfact16_7.shuffled | — | — | UNSAT 0.777s | UNSAT 0.794s | **UNSAT 0.775s** |
| ezfact16_8.shuffled | — | — | UNSAT 0.454s | UNSAT 0.461s | **UNSAT 0.441s** |
| ezfact32_2.shuffled | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| ezfact32_4.shuffled | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| ezfact32_9.shuffled | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| f10abbb7c1ae0e1a9ba7d575d9630d9a | — | **UNSAT 0.204s** | — | — | — |
| f2a0158e6029a7535611c6a8113daada | — | **UNSAT 6.6ms** | — | — | — |
| fclqcolor-08-06-06.shuffled-as.sat05-1265 | **SAT 2.3ms** | — | SAT 2.9ms | SAT 3.2ms | SAT 3.3ms |
| fec34da1be62ccac3d6ad60a513ce675 | — | **SAT 0.071s** | — | — | — |
| fphp-010-008.shuffled-as.sat05-1213 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| fphp-010-009.shuffled-as.sat05-1227 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| fphp-010-010.shuffled-as.sat05-1199 | SAT 1.7ms | — | **SAT 1.4ms** | SAT 1.6ms | SAT 1.5ms |
| fphp-012-012.shuffled-as.sat05-1200 | **SAT 2.2ms** | — | SAT 2.6ms | SAT 2.4ms | SAT 2.2ms |
| hcb2.shuffled-as.sat03-1430 | **UNSAT 0.5ms** | — | UNSAT 0.8ms | UNSAT 0.7ms | UNSAT 0.6ms |
| marg2x2.shuffled-as.sat03-1440 | UNSAT 0.8ms | — | UNSAT 0.7ms | **UNSAT 0.6ms** | UNSAT 0.7ms |
| marg2x3.shuffled-as.sat03-1441 | **UNSAT 5.7ms** | — | UNSAT 6.0ms | UNSAT 6.4ms | UNSAT 6.2ms |
| mod2-rand3bip-sat-200-1.shuffled-as.sat05-2143 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| mod2-rand3bip-sat-200-2.shuffled-as.sat05-2144 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| mod2-rand3bip-sat-200-3.shuffled-as.sat05-2145 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| mod2c-3cage-unsat-10-3.sat05-2568.reshuffled-07 | SAT 0.074s | — | SAT 0.072s | **SAT 0.071s** | SAT 0.073s |
| ph12 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| ph9 | — | — | UNSAT 2.06s | UNSAT 1.99s | **UNSAT 1.99s** |
| php-010-008.shuffled-as.sat05-1171 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| php-010-009.shuffled-as.sat05-1185 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| php-010-010.shuffled-as.sat05-1157 | SAT 0.8ms | — | SAT 0.9ms | **SAT 0.7ms** | SAT 0.8ms |
| php-012-012.shuffled-as.sat05-1158 | SAT 1.2ms | — | **SAT 1.1ms** | SAT 1.2ms | SAT 1.2ms |
| rope_0001.shuffled | **UNSAT 0.8ms** | — | UNSAT 1.0ms | UNSAT 1.2ms | UNSAT 0.8ms |
| urqh1c2x2.shuffled-as.sat03-1457 | UNSAT 2.7ms | — | UNSAT 2.4ms | **UNSAT 2.3ms** | UNSAT 2.6ms |
| urqh1c2x3.shuffled-as.sat03-1458 | UNKNOWN | — | UNSAT 47.29s | **UNSAT 43.44s** | UNSAT 46.17s |
| urqh2x2.shuffled-as.sat03-1470 | **SAT 0.6ms** | — | SAT 0.7ms | SAT 0.6ms | SAT 0.7ms |
| x1_16.shuffled | — | — | UNSAT 0.203s | UNSAT 0.200s | **UNSAT 0.192s** |
| x1_24.shuffled | — | — | **UNSAT 38.94s** | UNSAT 39.36s | UNSAT 40.17s |
| x1_32.shuffled | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x1_36.shuffled-as.sat03-1589 | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x2_16.shuffled | — | — | UNSAT 0.270s | UNSAT 0.261s | **UNSAT 0.251s** |
| x2_24.shuffled | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x2_32.shuffled | — | — | TIMEOUT 60.0s | TIMEOUT 60.0s | TIMEOUT 60.0s |
| x9-02007.sat.sanitized | — | — | **SAT 1.6ms** | SAT 1.7ms | SAT 2.0ms |
| x9-02021.sat.sanitized | — | — | **UNSAT 5.6ms** | UNSAT 5.6ms | UNSAT 5.7ms |
| x9-02023.sat.sanitized | — | — | **SAT 5.3ms** | SAT 5.4ms | SAT 5.6ms |
| x9-02036.sat.sanitized | — | — | UNSAT 6.2ms | UNSAT 6.3ms | **UNSAT 6.1ms** |
| x9-02042.sat.sanitized | — | — | UNSAT 7.8ms | UNSAT 7.7ms | **UNSAT 7.6ms** |
| x9-02043.sat.sanitized | — | — | **SAT 1.5ms** | SAT 1.5ms | SAT 1.5ms |
| x9-02044.sat.sanitized | — | — | SAT 3.5ms | SAT 3.5ms | **SAT 3.4ms** |
| x9-02053.sat.sanitized | — | — | UNSAT 9.1ms | UNSAT 9.1ms | **UNSAT 8.9ms** |
| x9-02073.sat.sanitized | — | — | UNSAT 7.6ms | **UNSAT 7.2ms** | UNSAT 7.8ms |
| x9-02090.sat.sanitized | — | — | SAT 5.4ms | **SAT 5.2ms** | SAT 5.4ms |
