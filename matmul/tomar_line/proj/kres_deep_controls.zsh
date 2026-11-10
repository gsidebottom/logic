#!/bin/zsh
# Controls for the deficient-case decider of kres (2026-11-10).  Reproduces, from a class representative REP.bits:
#   C3  reduce negatives: the k = 8 all-flattening-ranks-<= 6 subsets the SAT decider refuted (needs their list, arg 3)
#   C4  alt negatives / the k <= 7 all-dependent subsets (SAT: k <= 6 all unique; k = 7 mostly timeouts) (arg 4)
#   C1  planted reduction, delta = 1: a (7,7,7) k = 8 subset, two of its products split into three (same sum) -> 9 products
#   C2  planted reduction, delta = 2: the first (6,6,6) k = 8 subset (rank 8 by SAT), split likewise -> W of dim m+2
#   C5  planted alternatives: the split scheme has flippable pairs; every all-dependent k = 7 subset containing one must
#       show an alternative (or a reduction when it contains all three split products), the others must be unique
# usage: kres_deep_controls.zsh REP.bits reduce_needs_sat.txt alt_needs_sat.txt WORKDIR
set -u
L=/Users/greg/projects/logic; K=$L/target/release/kres; P=$L/matmul/tomar_line/proj
REP=$1; RNS=$2; ANS=$3; D=$4; mkdir -p "$D"
echo "=== C3: reduce negatives ($(wc -l < "$RNS" | tr -d ' ') SAT-refuted k=8 lines; expect all refuted)"
"$K" 4 4 4 "$REP" --lines "$RNS" --mode reduce --out "$D/C3.txt" | grep '^c k='
echo "=== C4: alt on the all-dependent k<=7 lists (expect all unique)"
"$K" 4 4 4 "$REP" --lines "$ANS" --mode alt --out "$D/C4.txt" | grep '^c k='
echo "=== C1: planted reduction, delta = 1"
"$K" 4 4 4 "$REP" --kmin 8 --kmax 8 --out "$D/R8.txt" | grep '^c k='
L1=$(grep -m1 'dims=7,7,7' "$D/R8.txt"); I1=${L1#*idx=}; p=${I1%%,*}; q=$(echo "$I1" | cut -d, -f2)
/usr/bin/python3 "$P/kres_ctrl.py" 4 4 4 "$REP" split "$p" "$q" "$D/ctrl_c1.bits"
"$K" 4 4 4 "$D/ctrl_c1.bits" --subset "$I1,47" | grep -v '^      new='
echo "R k=9 dims=7,7,7 idx=$I1,47" > "$D/c1_line.txt"; "$K" 4 4 4 "$D/ctrl_c1.bits" --lines "$D/c1_line.txt" --mode reduce --out "$D/c1_verdict.txt" | grep '^c k='
/usr/bin/python3 "$P/kres_apply.py" 4 4 4 "$D/ctrl_c1.bits" "$D/c1_verdict.txt" --out "$D/c1_apply" --tag c1
echo "=== C2: planted reduction, delta = 2"
L2=$(head -1 "$RNS"); I2=${L2#*idx=}; p=${I2%%,*}; q=$(echo "$I2" | cut -d, -f2)
/usr/bin/python3 "$P/kres_ctrl.py" 4 4 4 "$REP" split "$p" "$q" "$D/ctrl_c2.bits"
"$K" 4 4 4 "$D/ctrl_c2.bits" --subset "$I2,47" | grep -v '^      new='
echo "R k=9 dims=6,6,6 idx=$I2,47" > "$D/c2_line.txt"; "$K" 4 4 4 "$D/ctrl_c2.bits" --lines "$D/c2_line.txt" --mode reduce --out "$D/c2_verdict.txt" | grep '^c k='
/usr/bin/python3 "$P/kres_apply.py" 4 4 4 "$D/ctrl_c2.bits" "$D/c2_verdict.txt" --out "$D/c2_apply" --tag c2
echo "=== C5: planted alternatives in the split scheme (products $p -> X1, $q -> X2, 47 -> X3; X1,X2 share c; X2,X3 share a')"
"$K" 4 4 4 "$D/ctrl_c1.bits" --kmin 7 --kmax 7 --out "$D/c5_R7.txt" | grep '^c k='
"$K" 4 4 4 "$D/ctrl_c1.bits" --lines "$D/c5_R7.txt" --mode alt --out "$D/c5_verdict.txt" | grep '^c k='
/usr/bin/python3 - "$D/c5_R7.txt" "$D/c5_verdict.txt" "$D/ctrl_c1.bits" "${L1#*idx=}" <<'PYEOF'
import sys, collections
sys.path.insert(0, '/Users/greg/projects/logic/matmul')
from project_f2 import load_bits
al, be, ga = load_bits(sys.argv[3], 4, 4, 4); r = al.shape[0]
# every pair of products sharing a factor is flippable, hence an alternative for any subset containing it
shared = set()
for F in (al, be, ga):
    keys = {}
    for t in range(r): keys.setdefault(F[t].tobytes(), []).append(t)
    for v in keys.values():
        for i in v:
            for j in v:
                if i < j: shared.add((i, j))
print(f'  flippable pairs in the split scheme: {sorted(shared)}')
verd = {}
for l in open(sys.argv[2]):
    if l[:3] in ('RED', 'ALT', 'R k', 'A k'): verd[l.split('idx=')[1].split()[0]] = l.split()[0]
tab = collections.Counter()
for l in open(sys.argv[1]):
    if not l.startswith('R '): continue
    idx = l.split('idx=')[1].strip(); s = set(int(x) for x in idx.split(','))
    pair = any(i in s and j in s for i, j in shared)
    tab[('flippable pair present' if pair else 'no flippable pair', verd.get(idx, 'unique'))] += 1
for k, c in sorted(tab.items()): print(f'  {k[0]:24s} {k[1]:7s} {c}')
PYEOF
/usr/bin/python3 "$P/kres_apply.py" 4 4 4 "$D/ctrl_c1.bits" "$D/c5_verdict.txt" --out "$D/c5_apply" --tag c5 | grep -o 'rank [0-9]*, [a-z ]*' | sort | uniq -c
echo "=== done $(date '+%H:%M:%S')"
