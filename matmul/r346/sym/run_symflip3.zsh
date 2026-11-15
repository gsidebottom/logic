#!/bin/zsh
# symflip3 campaign (2026-11-15): the flip graph over F3 on <3x4x6> (target 53) and <3x3x6> (target 39), from the known
# schemes reduced mod 3 (seeds/*.trits, sym/to_trits.py) and from the standard schemes, plain and under index-permutation
# groups.  Sequential arms, 10 threads each, every arm capped.
cd /Users/greg/projects/logic
B=target/release/symflip3; S=matmul/r346/seeds; O=matmul/r346/sym/found3
arm() { echo; echo "=== $1"; shift; local m=$1; shift; timeout $(( m * 60 + 60 )) $B "$@" --minutes $m --threads 10; }
W="--plus 1 --plus-every 2000 --margin 8"; X="--plus 1 --plus-every 500 --margin 16"
arm "346: 54, plus near"      8 3 4 6 --start $S/3x4x6_m54.trits ${=W} --out $O/k54
arm "346: 54, plus wide"      5 3 4 6 --start $S/3x4x6_m54.trits ${=X} --seed 2 --out $O/k54w
arm "346: 56"                 3 3 4 6 --start $S/3x4x6_m56.trits --plus 0.5 --plus-every 5000 --margin 6 --out $O/k56
arm "346: 57"                 2 3 4 6 --start $S/3x4x6_m57.trits --plus 0.5 --plus-every 5000 --margin 6 --out $O/k57
arm "346: std plain"          4 3 4 6 --save-at 55 --out $O/std
arm "346: std Z3"             3 3 4 6 --save-at 55 --out $O/std_z3 --gen "1,2,0;0,1,2,3;1,2,0,4,5,3"
arm "346: std Z2xZ2"          3 3 4 6 --save-at 55 --out $O/std_v4 --gen "0,1,2;1,0,3,2;1,0,3,2,5,4" --gen "0,1,2;2,3,0,1;0,1,2,3,4,5"
arm "346: std Z6"             3 3 4 6 --save-at 55 --out $O/std_z6 --gen "1,2,0;1,0,3,2;1,2,3,4,5,0"
arm "336: 40 DPS, plus near"  6 3 3 6 --start $S/3x3x6_m40_dps.trits ${=W} --out $O/r40dps
arm "336: 40 DPS, plus wide"  4 3 3 6 --start $S/3x3x6_m40_dps.trits ${=X} --seed 2 --out $O/r40dpsw
arm "336: 40 original"        4 3 3 6 --start $S/3x3x6_m40_orig.trits ${=W} --out $O/r40orig
arm "336: 42"                 3 3 3 6 --start $S/3x3x6_m42.trits --plus 0.5 --plus-every 5000 --margin 6 --out $O/r42
arm "336: 43"                 2 3 3 6 --start $S/3x3x6_m43.trits --plus 0.5 --plus-every 5000 --margin 6 --out $O/r43
arm "336: std plain"          3 3 3 6 --save-at 41 --out $O/std336
echo "=== CAMPAIGN3 DONE"
