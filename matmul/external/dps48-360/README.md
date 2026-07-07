# A verified 360-operation rational <4x4x4:48> algorithm

Instance `Rt_Lt_Ptt_g2` — one of 18 S3-slot-variant x gauge images of
the Dumas–Pernet–Sedoglavic rational 4x4x4:48 scheme (arXiv
2506.13242, the de-complexified AlphaEvolve algorithm) produced by
`src/bin/cse48.rs` (Brent-verified at construction) — with each of its
three linear maps optimized by PLinOpt (Dumas–Grenet–Pernet–
Sedoglavic) and certified by PLinOpt's SLPchecker:

    L (side 1):   80 adds + 32 mults = 112
    R (side 2):  104 adds +  0 mults = 104
    P (output):  133 adds + 11 mults = 144
    TOTAL:       317 adds + 43 mults = 360   (+ 48 products)

Independently proven end to end by
`matmul/dps48/plinopt_stitch.py RtLtPtt_L.slp RtLtPtt_R.slp RtLtPtt_P.slp`:
exact Fractions, all 256 basis pairs (a complete proof of the bilinear
map), random integer trials, and a from-scratch operation recount.

**Update (2,000-rep converged run):** the same instance improved to a
**verified 357** (L = 79+33 = 112, R = 104+0, P = 136+5 = 141; files
`RtLtPtt_{L,R,P}_357.slp`, proven identically: 256/256 basis pairs,
recount matches SLPchecker). The original DPS instance under the same
budget: 364. The presentation gap is stable across budgets
(22 ops @ 24 reps, 8 @ 200, 7 @ 2,000).

Context: the DPS paper's published SLP totals 341; that number is not
reproduced by PLinOpt's shipped optimizer under any protocol we ran
(their own instance converges to 368 at 200 reps x 3 modes), so 341
presumably reflects additional compile-time options or compute. At
every equal-budget protocol our slot/gauge instances beat the original
instance (converged: 360 vs 368) — the representation handed to the
optimizer matters as much as the optimizer.
