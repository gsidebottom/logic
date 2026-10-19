#!/bin/sh
# Climb lbscan's whole-orbit lower bound for a scheme one target at a time,
# sharing one checkpoint; stop at the first target that is not proved.
# usage: sh lbclimb.sh PREFIX FIRST LAST OUTDIR [lbscan options...]
pre=$1; first=$2; last=$3; out=$4; shift 4
t=$first
while [ "$t" -le "$last" ]; do
  log="$out/climb_t$t.log"
  timeout 7200 ../../target/release/xor47 lbscan "$pre" --target "$t" --out "$out" "$@" > "$log" 2>&1
  if grep -q '^PROVED' "$log"; then
    echo "target $t: PROVED  ($(grep -o 'orbit lower bound proved.*' "$log"))"
  else
    echo "target $t: not proved -- $(grep -E '^NOT PROVED|budget' "$log" | head -2 | tr '\n' ' ')"
    break
  fi
  t=$((t + 1))
done
echo "CLIMB DONE"
