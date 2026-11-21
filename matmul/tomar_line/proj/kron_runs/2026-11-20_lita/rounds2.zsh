#!/bin/zsh
# rounds2.zsh LANE [FIRST_ROUND] (rounds.zsh with one kronkill per sequence above rank $SERIALM, default 9000): deletion chains from LITA's squares.  Every scheme in lanes/LANE/sources/rN gets
# the single deletions of the first and last index of every slot (first only above rank $BIG), each followed by
# the 2-reduction (kronkill modulo 1048573, bar = Sedoglavic's table of 2026-11-15).  For every shape the
# lowest result that also beats best.txt is replayed and certified over Q (kronexact) and becomes a source of
# the next round.  A shape that does not beat the published table is not expanded.
# Environment: MAXM (skip sources above this rank, default no limit), BIG (default 7000), RMAX (default 9).
D=${0:A:h}; cd $D/../..
P=$PWD; K=${P:h:h:h}/target/release/kronkill; X=${P:h:h:h}/target/release/kronexact; ST=$D/status_table_8e6ad05.json
lane=$1; r=${2:-2}; L=$D/lanes/$lane; MAXM=${MAXM:-1000000}; BIG=${BIG:-7000}; RMAX=${RMAX:-9}; SERIALM=${SERIALM:-9000}
mkdir -p $L/logs $D/exact; touch $D/best.txt
best() { awk -v s=$1 '$1==s && (b=="" || $2+0<b) {b=$2+0} END{print (b==""?1000000000:b)}' $D/best.txt }
while (( r <= RMAX )); do
  srcs=($L/sources/r$r/*.json(NoL)); (( $#srcs )) || break
  echo "$lane round $r: $#srcs sources, start $(date +%H:%M:%S)" >> $D/progress
  for f in $srcs; do
    tag=${f:t:r}; m=${${tag#*_m}%%_*}
    (( m > MAXM )) && { echo "$lane r$r $tag skipped (rank above $MAXM)" >> $D/progress; continue }
    n=(${(s:,:)$(head -c 300 $f | grep -o '"n":\[[0-9,]*\]' | head -1 | tr -d '"n:[]')})
    if (( m <= BIG )); then seqs="I0;J0;K0;I$((n[1]-1));J$((n[2]-1));K$((n[3]-1))"; else seqs="I0;J0;K0"; fi
    s=$(date +%s)
    if (( m <= SERIALM )); then
      timeout 14400 $K $f "$seqs" --walk 100 --restarts 4 --status $ST --out $L/logs/r${r}__$tag.csv --paths $L/paths/r$r/$tag > $L/logs/r${r}__$tag.log 2>&1
    else   # one sequence at a time: bounded memory
      : > $L/logs/r${r}__$tag.log
      for q in ${(s:;:)seqs}; do
        timeout 14400 $K $f $q --walk 100 --restarts 4 --status $ST --out $L/logs/r${r}__${tag}__$q.csv --paths $L/paths/r$r/$tag >> $L/logs/r${r}__$tag.log 2>&1
      done
    fi
    echo "$lane r$r $tag exit $? $(( $(date +%s) - s )) s: $(grep -o -- '[0-9]*x[0-9]*x[0-9]* [IJK][0-9]*: .* -> [0-9]*; catalog Q [0-9]*' $L/logs/r${r}__$tag.log | sed 's/ [IJK][0-9]*: .* -> / /; s/; catalog Q / vs /' | sort | uniq -c | tr '\n' ';' | tr -s ' ')" >> $D/progress
  done
  # the lowest path of every shape over the round's sources, if it beats what is certified already
  todo=($(ls $L/paths/r$r/*/*.path.json 2>/dev/null | awk -F/ '{f=$NF; s=f; sub(/_m.*/,"",s); m=f; sub(/^[^_]*_m/,"",m); sub(/_.*/,"",m); if(!(s in b) || m+0<b[s]) {b[s]=m+0; p[s]=$0}} END{for(s in p) print p[s]}'))
  mkdir -p $L/sources/r$((r+1))
  for pj in $todo; do
    stem=${${pj:t}%.path.json}; shape=${stem%%_m*}; m=${${stem#*_m}%%_*}
    (( m < $(best $shape) )) || continue
    out=$D/exact/${shape}_m${m}_Q.json; log=$D/exact/${shape}_m${m}.log
    src=$(python3 -I -c "import json,sys; print(json.load(open(sys.argv[1]))['source'])" $pj)
    s=$(date +%s)
    timeout 14400 $X replay $src $pj $out > $log 2>&1
    rc=$?
    if [[ $rc -eq 0 && -f $out ]] && grep -q 'VERIFIES EXACTLY; corrupted copy REJECTED' $log; then
      echo "$shape $m" >> $D/best.txt
      cp $out $L/sources/r$((r+1))/${shape}_m${m}_Q.json; gzip -f $out; cp $pj $D/exact/${shape}_m${m}_Q.path.json
      echo "VERIFIED $shape $m from ${src:t} ${stem##*_m${m}_}: $(grep -o 'denominator primes.*' $log | tail -1) ($(( $(date +%s) - s )) s)" >> $D/verified.txt
    else
      echo "NOT VERIFIED $shape $m from ${src:t} $stem exit $rc: $(grep -E 'panicked|DOES NOT|assert' -A1 $log | tail -1 | cut -c1-160)" >> $D/verified.txt
    fi
  done
  # (the plain copies in sources/ duplicate exact/*.json.gz; nothing is deleted here)
  echo "$lane round $r done $(date +%H:%M:%S)" >> $D/progress
  r=$((r+1))
done
echo "$lane ALL DONE $(date)" >> $D/progress; touch $L/finished
