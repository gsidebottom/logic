#!/bin/sh
# exhaustive orbit scan + exact refinement for the top mixed schemes
for m in 00084 00002 00009 00029 00037; do
  python3 ../x47/scheme47.py tosms mix/mix-$m.bits f2/mix$m > /dev/null
  timeout 3600 ../../target/release/xor47 scan f2/mix$m --runs 1 --depth 2 --threads 12 --seed 9 --out out/scan_mix$m > out/scan_mix$m.log 2>&1
  timeout 1800 ../../target/release/xor47 refine f2/mix$m out/scan_mix$m/scan_cands.txt --runs 100 --cap 60 --threads 12 --seed 3 --out out/refine_mix$m > out/refine_mix$m.log 2>&1
  echo "mix-$m: scan $(grep -o 'orbit minimum[^;]*' out/scan_mix$m.log | head -1) | refined best $(grep '^best' out/refine_mix$m.log | awk '{print $2}') | open sides $(grep '^point' out/refine_mix$m.log | grep -c '?')"
done
echo "ALL DONE"
