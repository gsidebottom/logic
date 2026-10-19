#!/bin/sh
# Whole-orbit screen against the 156 record: `xor47 lbscan --target 156`
# on each scheme of a list of .bits files.  PROVED means no point of that
# scheme's orbit beats 156; "genuine" triples (all three sides exact)
# would be F2 points below 156.  Resumable: finished logs are skipped.
# usage: sh lbscreen.sh LIST OUTDIR [lbscan options...]
list=$1; out=$2; shift 2
mkdir -p "$out/sms"
while read -r bits; do
  name=$(basename "$(dirname "$bits")")_$(basename "$bits" .bits)
  pre="$out/sms/$name"
  [ -f "${pre}_L.sms" ] || python3 ../x47/scheme47.py tosms "$bits" "$pre" > /dev/null
  log="$out/$name.log"
  if ! { [ -f "$log" ] && grep -q -E '^(PROVED|NOT PROVED)' "$log"; }; then
    timeout 1800 ../../target/release/xor47 lbscan "$pre" --target 156 --out "$out/$name" "$@" > "$log" 2>&1
  fi
  bound=$(grep -o 'every point costs at least [0-9]*' "$log" | tail -1 | grep -o '[0-9]*$')
  res=$(grep -E '^PROVED|^NOT PROVED' "$log" | head -1 | sed -E 's/^NOT PROVED: ([0-9]+) coset triples.*: ([0-9]+) with all three sides exact.*, ([0-9]+) with an open side.*/NOT PROVED: \1 triples, \2 genuine, \3 open/; s/^PROVED.*/PROVED/')
  echo "$name ${bound:-?} ${res:-TIMEOUT}"
done < "$list"
echo "SCREEN DONE"
