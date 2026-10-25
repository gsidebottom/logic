#!/bin/bash
# the Rust search at scale: Table 1's scheme 10,000 starts per role; DPS25 and our 201 point
# 2,400 per role (same orbit or not)
cd "$(dirname "$0")/../../.." || exit 1
D=matmul/dps48/plinopt/data
G=matmul/dps48/gamma
echo "# gamma48 at scale $(date '+%Y-%m-%d %H:%M')"
for r in 0 1 2; do ./target/release/gamma48 $D/4x4x4_48_accurate $r 10000 $((1000000 * (r + 1))) --out $G/rs10k_table1_r$r.txt; done
for r in 0 1 2; do ./target/release/gamma48 $D/4x4x4_48_rational $r 2400 $((5000000 + 100000 * r)) --out $G/rs_dps25_r$r.txt; done
for r in 0 1 2; do ./target/release/gamma48 matmul/dps48/cand48/p005_201n $r 2400 $((7000000 + 100000 * r)) --out $G/rs_ours201_r$r.txt; done
echo "# done $(date '+%H:%M')"
