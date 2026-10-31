#!/bin/bash
# LNS on the product-rescaled variants of the 203 point: 12 naive seeds x 180 s per matrix.  P is
# searched through its transpose (Tellegen: cost(P) = cost(P^T) + 32).  Pt_base is the control.
SP=/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad
LNS=/Users/greg/projects/logic/target/release/lns48
cd $SP/rfc2610/lns
echo "# lns48 on the rescaled variants, $(date '+%Y-%m-%d %H:%M')"
for m in Pt_base L_all2 R_all2 Pt_all_d2 Pt_all_d4 L_p43x2 R_p43x2 Pt_p43_d2 Pt_p43_d4; do
  mkdir -p r_$m
  $LNS --sms $SP/rfc2610/resc/$m.sms --out r_$m --wall 180 --seeds 12 --log 90 > r_$m.log 2>&1
  echo "$m exit $? $(date '+%H:%M'): $(grep '^final' r_$m.log | cut -c1-110)"
done
echo "# done $(date '+%H:%M')"
