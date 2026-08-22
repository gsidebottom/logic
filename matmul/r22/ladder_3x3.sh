#!/bin/bash
# Rank ladder from the easy (far-below-threshold) side: certified
# hydra_satsuma on brent_3x3x{r}.cnf, 30 min bound each, in parallel.
cd "$(dirname "$0")/../.."
python3 - <<'PY'
import sys; sys.path.insert(0, 'matmul')
from brent import to_cnf, write_dimacs
for r in (9, 12, 15, 17, 18, 19, 20):
    nv, cls = to_cnf(3, 3, 3, r)
    write_dimacs(f"matmul/r22/brent_3x3x{r}.cnf", nv, cls)
PY
for r in 9 12 15 17 18 19 20; do
  ( nice -n 8 ./target/release/sat -b hydra_satsuma --timeout 1800 --proof matmul/r22/brent_3x3x${r}.sr \
      < matmul/r22/brent_3x3x${r}.cnf > matmul/r22/brent_3x3x${r}_hs.out 2> matmul/r22/brent_3x3x${r}_hs.err;
    echo "EXIT=$?" >> matmul/r22/brent_3x3x${r}_hs.err ) &
done
wait
for r in 9 12 15 17 18 19 20; do
  echo "r=$r: $(head -1 matmul/r22/brent_3x3x${r}_hs.out) | $(grep -oE 'UNSAT in [0-9.]+ms|SAT in [0-9.]+ms|TIMEOUT after [0-9.]+ms' matmul/r22/brent_3x3x${r}_hs.err | head -1) | $(grep -oE 'dsr-trim VERIFIED UNSAT|dsr-trim verify [0-9.]+s total' matmul/r22/brent_3x3x${r}_hs.err | tr '\n' ' ')"
done
echo "LADDER DONE"
