# 166 XORs for <4x4x4:47> over F2 (2026-11-08)

Two programs with 166 XORs in total (L + R + P, the output side priced
through its transpose: P = Pt + 31), one below the 167 of `../x167`
(Kauers-Moosbauer class, 2026-10-17) and four below PLinOpt's published 170.
Both are points in the GL(4,2)^3 orbit of the fifth rank-47 class
(`../../seeds/projkm47_7`, representative
matmul/tomar_line/proj/found47_km56/d180/r47-00007.bits, reached on
2026-11-07 by the flip descent from the <4,4,5>:60 projection pool).

| files | coset triple (X, Y, Z) | L | R | P (= Pt + 31) | total |
|---|---|---|---|---|---|
| `x166a_{L,R,P}.{sms,slp}`, `x166a.bits` | 34f1 1e25 163d | 44 | 48 | 74 (43) | 166 |
| `x166b_{L,R,P}.{sms,slp}`, `x166b.bits` | 135c 7831 79a8 | 43 | 48 | 75 (44) | 166 |

At both points all three sides are exact (the helper search refuted one
fewer helper on each): Boyar-Peralta gives 49 on both R sides, the exact
minimum is 48, and that single gain is the record.  Within the 283 orbit
points at heuristic total 167 or 168 nothing can go below 166
(`settle_top168.log`: 174 distinct open sides, depth 12, cap 600 s, 1572 s,
"points still open below it: 0").

How they were found: `xor47 scan seeds/projkm47_7 --runs 1 --depth 4`
(fresh tables, heuristic orbit minimum 167 at 3 of the 840 X-cosets, 4493
triples within +4), `xor47 refine` on those (167 at 32 triples, 168 at 251;
`refine_top168_points.log`), `xor47 settle` on the 283 (the 166s),
then `xor47 refine --cap 1800` on each triple alone (`cands166a.txt`,
`cands166b.txt`) to emit the programs.

Checks (all from scratch, nothing shared with xor47):
- `python3 -I ../../x47check.py best/x166/x166a` and `x166b` (run from
  matmul/x47): every SLP computes its matrix, the XOR counts are as stated,
  and (L, R, P) multiplies all 256 pairs of 4x4 basis matrices over F2.
- PLinOpt `SLPchecker -q 2 -M x166a_L.sms x166a_L.slp` etc.: SUCCESS for all
  six programs, three rounds each (the checker is a random test).
- Class: both `.bits` are exactly de Groote-equivalent to r47-00007
  (matmul/tomar_line/proj/scheme_iso.py, certificates in the sandwich maps).

The rest of the window (4210 triples at heuristic 169-171) was then settled
at target 166 (`settle4_window.log`: depth 8, cap 600 s, 1491 sides, 2 h
22 min, 108 points left open below 166; `settle4b_window.log`: depth 12, cap
60 s, 2 min, none left): 166 is exact over all 4493 triples within +4 of the
scan minimum, and exactly the two triples above reach it.

Open: no whole-orbit lower bound for this class has been climbed yet (the
window is relative to the heuristic minimum; a coset triple outside it could
in principle cost less).

Contributed to PLinOpt as https://github.com/jgdumas/plinopt/pull/39 (2026-11-09; branch
data-4x4x4-47-166 on gsidebottom/plinopt): data/4x4x4_47_mod_2_166_{L,R,P} = x166a and
data/4x4x4_47_mod_2_166b_{L,R,P} = x166b, checked there with SLPchecker -q 2 and 40 runs of
MMchecker -q 2 each; PR text in the style of #22 (the 167).
