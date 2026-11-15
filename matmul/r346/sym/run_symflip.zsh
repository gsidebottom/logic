#!/bin/zsh
# symflip campaign on <3x4x6> (2026-11-14): index-permutation groups from the standard scheme, and the known 54's
# own symmetry subgroups (over F2, order 18) from the 54.  Sequential arms, 10 threads each, every arm capped.
cd /Users/greg/projects/logic
B=target/release/symflip; S=matmul/r346/seeds; O=matmul/r346/sym/found
arm() { echo; echo "=== $1"; shift; timeout $(( $1 * 60 + 60 )) $B 3 4 6 --minutes "$@" --threads 10; }
arm "std plain"            3 --save-at 55 --out $O/std_plain
arm "std Z3 rows+cols"     3 --save-at 55 --out $O/std_z3   --gen "1,2,0;0,1,2,3;1,2,0,4,5,3"
arm "std Z2 inner+cols"    3 --save-at 55 --out $O/std_z2a  --gen "0,1,2;1,0,3,2;1,0,3,2,5,4"
arm "std Z2 rows+cols"     3 --save-at 55 --out $O/std_z2b  --gen "1,0,2;0,1,2,3;3,4,5,0,1,2"
arm "std S3 rows+cols"     3 --save-at 55 --out $O/std_s3   --gen "1,2,0;0,1,2,3;1,2,0,4,5,3" --gen "1,0,2;0,1,2,3;1,0,2,4,3,5"
arm "std Z2xZ2 inner"      3 --save-at 55 --out $O/std_v4   --gen "0,1,2;1,0,3,2;1,0,3,2,5,4" --gen "0,1,2;2,3,0,1;0,1,2,3,4,5"
arm "std Z6"               3 --save-at 55 --out $O/std_z6   --gen "1,2,0;1,0,3,2;1,2,3,4,5,0"
# from the 54 (no two of its summands share a factor: every walk starts with plus transitions)
K="--start $S/3x4x6_m54_ZT.bits --save-at 53 --plus 1 --plus-every 2000"
arm "54 plain"             3 ${=K} --margin 8 --out $O/k54_plain
arm "54 Z2 (elem 0)"       3 ${=K} --margin 8 --aut --use 0 --out $O/k54_z2
for e in 3 4 5 6; do
arm "54 Z3 (elem $e)"      3 ${=K} --margin 12 --aut --use $e --out $O/k54_z3_$e
done
arm "54 two order-3"       3 ${=K} --margin 18 --aut --use 3,4 --out $O/k54_33
arm "54 order 2 + order 3" 3 ${=K} --margin 12 --aut --use 0,3 --out $O/k54_23
arm "54 full group"        3 ${=K} --margin 36 --aut --out $O/k54_full
arm "56 Z2"                3 --start $S/3x4x6_m56_ZT.bits --aut --use 0 --save-at 55 --plus 0.5 --plus-every 5000 --margin 6 --out $O/k56_z2
arm "56 plain"             3 --start $S/3x4x6_m56_ZT.bits --save-at 55 --plus 0.5 --plus-every 5000 --margin 6 --out $O/k56_plain
echo "=== CAMPAIGN2 DONE"
