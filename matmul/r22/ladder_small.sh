#!/bin/bash
# Sequential small-rank ladder r=1..8 on 3x3: certified hydra_satsuma,
# 600 s bound each, stop at the first timeout (larger r only gets harder).
cd "$(dirname "$0")/../.."
python3 - <<'PY'
import sys; sys.path.insert(0, 'matmul')
from brent import to_cnf, write_dimacs, var_counts
for r in range(1, 9):
    nv, cls = to_cnf(3, 3, 3, r)
    write_dimacs(f"matmul/r22/brent_3x3x{r}.cnf", nv, cls)
    print(f"brent_3x3x{r}.cnf: base vars {sum(var_counts(3,3,3,r))}, cnf {nv} vars / {len(cls)} clauses")
PY
for r in 1 2 3 4 5 6 7 8; do
  nice -n 5 ./target/release/sat -b hydra_satsuma --timeout 600 --proof matmul/r22/brent_3x3x${r}.sr \
      < matmul/r22/brent_3x3x${r}.cnf > matmul/r22/brent_3x3x${r}_hs.out 2> matmul/r22/brent_3x3x${r}_hs.err
  rc=$?; echo "EXIT=$rc" >> matmul/r22/brent_3x3x${r}_hs.err
  echo "r=$r: $(head -1 matmul/r22/brent_3x3x${r}_hs.out) | $(grep -oE 'UNSAT in [0-9.]+ms|SAT in [0-9.]+ms|TIMEOUT after [0-9.]+ms' matmul/r22/brent_3x3x${r}_hs.err | head -1) | $(grep -oE 'dsr-trim VERIFIED UNSAT|dsr-trim verify [0-9.]+s total' matmul/r22/brent_3x3x${r}_hs.err | tr '\n' ' ')"
  if grep -q TIMEOUT matmul/r22/brent_3x3x${r}_hs.err; then echo "stopping at r=$r (timeout)"; break; fi
done
echo "SMALL LADDER DONE"
