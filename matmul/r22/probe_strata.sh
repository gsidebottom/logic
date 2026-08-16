#!/bin/bash
cd "$(dirname "$0")/../.."
for s in S0_r21 S1_rank1 S2_rank2 S3_rank3; do
  ( nice -n 8 ./target/release/sat -b hydra_satsuma --timeout 7200 --proof matmul/r22/${s}.sr \
      < matmul/r22/${s}.cnf > matmul/r22/${s}_probe.out 2> matmul/r22/${s}_probe.err ) &
done
wait
for s in S0_r21 S1_rank1 S2_rank2 S3_rank3; do
  echo "$s: $(grep -E '^s ' matmul/r22/${s}_probe.out) $(grep -oE 'VERIFIED UNSAT|TIMEOUT after [0-9.]+ms' matmul/r22/${s}_probe.err | head -1)"
done
