#!/bin/zsh
# Positive controls for the depth-2 decider of kres (2026-11-10 13:00): planted reductions and alternatives two dimensions
# short.  usage: kres_depth2_controls.zsh OPEN_LINES.txt CTRL_DIR OUT_DIR [KRES]
#   OPEN_LINES: the open alternatives lines (A ...) of a class whose products 0 and 1 are the split pair of CTRL_DIR's
#               ctrl_c2.bits (kres_ctrl.py split 0 1) and the flip-planted pair of ctrl_c1.bits (kres_deep_controls.zsh)
#   CTRL_DIR:   holds ctrl_c1.bits, ctrl_c2.bits and c5_verdict.txt from kres_deep_controls.zsh
# C: every open line containing products 0 and 1, with the third split product (index 47) appended, is a subset of the
#    split scheme whose residual has a decomposition with one term fewer (the original pair): expect REDUCIBLE wherever
#    the chosen direction is at most two dimensions short, open (R) beyond, never refuted.
# Cr: 3000 random k=9 subsets {0,1,47} + 6 of the split scheme: all REDUCIBLE (mostly exact or one short).
# D: the open (A) lines of the planted-flip control (two dimensions short, all containing the three split products):
#    all positive (RED or ALT) at depth 2.
set -u
OPEN=$1; C=$2; D=$3; K=${4:-/Users/greg/projects/logic/target/release/kres}; mkdir -p "$D"
/usr/bin/python3 - "$OPEN" "$D" <<'PY'
import sys,random
src,D=sys.argv[1],sys.argv[2]
red=[]
for line in open(src):
    p=line.find('idx='); idx=[int(x) for x in line[p+4:].split()[0].split(',')]
    if 0 in idx and 1 in idx: red.append('R k=%d idx=%s'%(len(idx)+1,','.join(map(str,idx+[47]))))
open(D+'/C_lines.txt','w').write('\n'.join(red)+'\n'); print('C:',len(red),'lines')
random.seed(20261110); seen=set(); out=[]
while len(out)<3000:
    t=tuple(sorted(random.sample(range(2,47),6)))
    if t in seen: continue
    seen.add(t); out.append('R k=9 idx='+','.join(map(str,(0,1)+t+(47,))))
open(D+'/Cr_lines.txt','w').write('\n'.join(out)+'\n'); print('Cr: 3000 lines')
PY
grep '^A ' "$C/c5_verdict.txt" > "$D/D_lines.txt"; echo "D: $(wc -l < "$D/D_lines.txt") lines"
echo "=== C: planted reductions (expect REDUCIBLE or open, none refuted)"
"$K" 4 4 4 "$C/ctrl_c2.bits" --lines "$D/C_lines.txt" --mode reduce --threads 12 --out "$D/C_verdicts.txt" | grep -E '^c k='
echo "  written: $(cut -d' ' -f1 "$D/C_verdicts.txt" | sort | uniq -c | tr '\n' ' ') of $(wc -l < "$D/C_lines.txt"); verified: $(grep -o 'verified=[01]' "$D/C_verdicts.txt" | sort | uniq -c | tr '\n' ' ')"
echo "=== Cr: random planted reductions (expect 3000 REDUCIBLE)"
"$K" 4 4 4 "$C/ctrl_c2.bits" --lines "$D/Cr_lines.txt" --mode reduce --threads 12 --out "$D/Cr_verdicts.txt" | grep -E '^c k='
echo "=== D: planted-flip lines two dimensions short (expect all RED or ALT)"
"$K" 4 4 4 "$C/ctrl_c1.bits" --lines "$D/D_lines.txt" --mode alt --maxdelta-alt 2 --threads 12 --out "$D/D_verdicts.txt" | grep -E '^c k='
echo "  written: $(cut -d' ' -f1 "$D/D_verdicts.txt" | sort | uniq -c | tr '\n' ' ') of $(wc -l < "$D/D_lines.txt"); verified: $(grep -o 'verified=[01]' "$D/D_verdicts.txt" | sort | uniq -c | tr '\n' ' ')"
