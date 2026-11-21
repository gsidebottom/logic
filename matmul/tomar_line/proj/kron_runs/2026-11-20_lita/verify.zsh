#!/bin/zsh
# verify.zsh PATHDIR...: for every shape with a path file in the given directories, the lowest-rank path is
# replayed exactly over Q and certified by target/release/kronexact (every Brent equation in integers, with a
# corrupted-copy control).  Certified schemes land in exact/ (gzip), one line each in verified.txt.
cd ${0:A:h}/../..
D=kron_runs/2026-11-20_lita; X=../../../target/release/kronexact
mkdir -p $D/exact
for dir in "$@"; do
  # lowest m per shape
  for pj in $(ls $dir/*.path.json 2>/dev/null | awk -F/ '{f=$NF; s=f; sub(/_m.*/,"",s); m=f; sub(/^[^_]*_m/,"",m); sub(/_.*/,"",m); if(!(s in b) || m+0<b[s]) {b[s]=m+0; p[s]=$0}} END{for(s in p) print p[s]}'); do
    stem=${${pj:t}%.path.json}; shape=${stem%%_m*}; m=${${stem#*_m}%%_*}
    out=$D/exact/${shape}_m${m}_Q.json
    [[ -f $out.gz ]] && continue
    src=$(python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))['source'])" $pj)
    s=$(date +%s)
    timeout 14400 $X replay $src $pj $out > $D/exact/${shape}_m${m}.log 2>&1
    rc=$?
    if [[ $rc -eq 0 && -f $out ]] && grep -q 'VERIFIES EXACTLY; corrupted copy REJECTED' $D/exact/${shape}_m${m}.log; then
      gzip -f $out; cp $pj $D/exact/${shape}_m${m}_Q.path.json
      echo "VERIFIED $shape $m from ${src:t} ${stem##*_m${m}_}: $(grep -o 'denominator primes.*' $D/exact/${shape}_m${m}.log | tail -1) ($(( $(date +%s) - s )) s)" >> $D/verified.txt
    else
      echo "NOT VERIFIED $shape $m from ${src:t} $stem exit $rc: $(grep -E 'panicked|DOES NOT|assert' -A1 $D/exact/${shape}_m${m}.log | tail -1 | cut -c1-160)" >> $D/verified.txt
    fi
  done
done
echo "verify done $* $(date +%H:%M:%S)" >> $D/progress
