#!/bin/zsh
# Materialize the 20-instance cxlb benchmark set described in
# doc/matmul_cxlb_satcomp.md (deterministic; regenerable anytime).
set -eu
cd /Users/greg/projects/logic
OUT=${1:-matmul/found55/satcomp}
mkdir -p $OUT
PY=.venv/bin/python
gen() { # gen <bits> <k> <sb|nosb> <name>
  local flags=""
  [ "$3" = "nosb" ] && flags="--no-sb"
  $PY matmul/cxlb.py --bits $2 --k $4 --dump $OUT/$1-k$4-$3.cnf \
      ${=flags} > /dev/null
  echo "  $1-k$4-$3.cnf"
}
echo "== seed cells (boundary +-1) =="
for k in 28 29 30; do
  for sb in sb nosb; do gen sun56 matmul/perminov_cache/bits/sun56.bits $sb $k; done
done
for k in 26 27 28; do
  for sb in sb nosb; do gen cn120 matmul/perminov_cache/bits/cr58-cn120.bits $sb $k; done
done
echo "== other 56-class identity cells =="
for sb in sb nosb; do gen i19 matmul/external/i19-perminov56.bits $sb 28; done
for sb in sb nosb; do gen i12 matmul/external/i12-orbit56.bits $sb 28; done
echo "== fat-sides window cells of the record class @ k=27 =="
FDIR=$OUT/fatcells
rm -rf $FDIR && mkdir -p $FDIR
./target/release/floors matmul/perminov_cache/bits/sun56.bits \
    --variants 1 --emit-sides 29 --emit-cands $FDIR --threads 10 \
    > /dev/null 2>&1
i=0
for f in $(ls $FDIR/*.bits | sort | head -4); do
  i=$((i+1))
  gen sunfat$i $f sb 27
done
rm -rf $FDIR
n=$(ls $OUT/*.cnf | wc -l | tr -d ' ')
echo "generated $n instances in $OUT"
