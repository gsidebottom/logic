#!/bin/zsh
# Used 2026-11-11 to verify 13x14x14 m1564 and 15x16x16 m2202 (logs in kron_reduced/ and logs/).
# verify_one.zsh SRC.json OUTDIR STEM PROJECTION-FLAGS...  (e.g. --I 7)
# exact projection (kron_project.py), pivot search on THAT file (kron_kill.py), exact replay (kron_reduce.py --pivots),
# independent check (scheme_semantic_check.py).  One-step paths only; a longer path is reported and left for a manual replay.
set -u
SRC=$1; OUT=$2; STEM=$3; shift 3
R=/Users/greg/projects/logic/matmul/tomar_line/proj
cd "$R" || exit 1
date "+start $STEM %H:%M:%S"
/usr/bin/python3 -I kron_project.py "$SRC" "$OUT/${STEM}_proj.json" "$@" || exit 1
nice -n 5 /opt/homebrew/bin/timeout 1800s /usr/bin/python3 kron_kill.py "$OUT/${STEM}_proj.json" --trials 3 --seed 7 --walk 400 --out "$OUT/kill_${STEM}" || exit 1
PV=$(/usr/bin/python3 -I -c "import json,sys; d=json.load(open(sys.argv[1])); s=d['steps']; print(len(s), d['m_out'], s[0]['direction'], ','.join(map(str,s[0]['pivots'])))" "$OUT/kill_${STEM}.path.json")
read NST MOUT DIR PIV <<< "$PV"
echo "path: ${NST} step(s), best ${MOUT}, first direction ${DIR} $(date '+%H:%M:%S')"
if [[ "$NST" != 1 ]]; then echo "LONGER PATH: replay by hand"; exit 2; fi
nice -n 5 /opt/homebrew/bin/timeout 1800s /usr/bin/python3 kron_reduce.py "$OUT/${STEM}_proj.json" "${DIR}" "$OUT/${STEM}_m${MOUT}_Q.json" --pivots "${PIV}" || exit 1
/usr/bin/python3 -I scheme_semantic_check.py "$OUT/${STEM}_m${MOUT}_Q.json" 2 11
date "+end $STEM %H:%M:%S"
