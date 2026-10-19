#!/bin/sh
# Whole-orbit lower bound for one rank-47 class, the way the KM class was
# done: raise helper levels 1-2 on every deficient set at the final target
# (a minute), then climb the target one step at a time (lbclimb.sh) on the
# shared checkpoint until a step exceeds its budget.
# usage: sh lbclass.sh CLASS START [TARGET]   (CLASS = seeds/CLASS, e.g. at47)
# Caps: pre-raise 30 min; per climb step --budget 3.5 h (+1 h for the last
# test); whole climb 12 h.
c=$1; start=$2; target=${3:-167}
out="out/lb$c/t$target"
mkdir -p "$out"
timeout 2400 ../../target/release/xor47 lbscan "seeds/$c" --target "$target" --depth 2 --cap 60 --budget 1800 --threads 12 --out "$out" > "out/lb$c/preraise.log" 2>&1
echo "$c pre-raise: $(grep -o 'orbit lower bound proved.*' "out/lb$c/preraise.log")"
LBTIMEOUT=16500 timeout 43200 sh lbclimb.sh "seeds/$c" "$start" "$target" "$out" --depth 9 --cap 3600 --chunk 2000 --threads 12 --budget 12600
