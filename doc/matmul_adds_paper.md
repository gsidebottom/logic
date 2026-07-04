# Three New 60-Addition, Rank-23 Schemes for 3×3 Matrix Multiplication

*Research note — logic repo, matmul track, 2026-07-03; revised
2026-07-04 after Perminov (arXiv:2512.21980, Dec 2025) came to our
attention — the additive record is now **58**, not 60; framing updated
throughout, findings unchanged. Companion to
`doc/matmul_53_3x3_schemes.md`; every claim has a mechanical check (§6).*

---

## Abstract

The additive-complexity record for exact non-commutative 3×3 matrix
multiplication with 23 multiplications is **58 additions** without
change of basis (Perminov, arXiv:2512.21980, Dec 2025 — ternary
flip-graph search + greedy intersection CSE), which superseded
Stapleton's 60 (arXiv:2508.03857, Aug 2025; prior: 61 with basis change,
Schwartz–Vaknin 2023; 62 without, Mårtensson–Wagner 2024). This note's
results were obtained against the 60-era frontier and are reframed
accordingly. We report:

1. **Three further schemes achieving 60 additions**, on three mutually
   inequivalent de Groote classes distinct from Stapleton's — so at
   least four inequivalent rank-23 classes attain what was the record
   count until Dec 2025. Each is presented as a replay-verified
   straight-line program (one in full in the appendix).
2. **A classification of Stapleton's scheme**: it is de Groote-equivalent
   to scheme `i2w201c26fi-000` of the Heule–Kauers–Seidl (HKS) database —
   his neural pipeline rediscovered a class published in 2019. (No such
   check appears in the note; ours is exact, with an equivalence witness.)
3. **The observation that makes the search productive**: the optimized
   addition count is **not** a de Groote invariant. Within Stapleton's
   own class, the database's stored representative plateaus at 62 while
   his representative attains 60; our three schemes were found by
   *climbing the group orbit* with the CSE count as objective, after a
   **full-database screen** (all 17,376 HKS schemes — apparently the
   first such sweep) surfaced three classes whose lazy representatives
   already reached 61.
4. **A characterization of our search family's ceiling at 60**: all
   four classes plateau at exactly 60 under greedy signed-pair CSE ×
   enumerated sign models (SAT) × randomized restarts × orbit walks
   with transvection moves (>20,000 well-mixed proposals per class).
   At the time we wrote, honestly, that this was "either a true barrier
   at 60 or a shared ceiling of the greedy-CSE family" — Perminov's 58
   resolves it: it was the family ceiling. The finding stands as a
   clean negative about this heuristic family (§7).

## 1. Cost model and history

A bilinear scheme with r products computes M_m = P_m·Q_m from linear
forms P_m (over the 9 entries of A), Q_m (over B), then each C entry as a
linear form over the M_m. The **additive complexity** is the number of
binary additions/subtractions in a straight-line program computing all
forms; unary negation is free; no change of basis (Karstadt–Schwartz
style accounting is *not* used). This is exactly the model of
Mårtensson–Wagner and Stapleton; Schwartz–Vaknin's 61 lives in the
weaker with-basis-change model.

| year | count | scheme / method | basis change |
|---|---|---|---|
| 1976 | 98 | Laderman, naive form | — |
| 2023 | 61 | Schwartz–Vaknin (pebbling + alt. basis) | **yes** |
| 2024 | 62 | Mårtensson–Wagner, Greedy-Potential on Laderman | no |
| 2025 (Aug) | 60 | Stapleton (NN-discovered scheme + Greedy-Potential) | no |
| this note (Jul 2026, vs the 60-era frontier) | 60 × 3 more classes | HKS DB classes + orbit-CSE | no |
| **2025 (Dec)** | **58 — current record** | Perminov (ternary flip-graph + intersection CSE), arXiv:2512.21980 | no |

## 2. Tools (all in `matmul/`, all verification-gated)

- **`slp.py`** — greedy signed-pair CSE (Boyar–Peralta flavored): extract
  the most frequent signed variable pair, substitute, repeat; remaining
  forms cost |form|−1. Every emitted count is **replay-verified**: the
  recorded trace is symbolically expanded and must reproduce the exact
  signed forms. Two search axes on top: **sign-model enumeration** (a
  scheme's ±1 signs are the solutions of a sign-SAT instance; distinct
  models are enumerated with blocking clauses — different sign models CSE
  differently) and **randomized tie-breaking restarts**.
- **`equiv.py`** — exact de Groote equivalence. In the (α, β, γᵀ)
  representation the symmetry group acts as the cyclic sandwich
  (PAQ⁻¹, QBR⁻¹, RC̃P⁻¹), making every summand-matching constraint
  *linear* in the 27 GF(2) unknowns of (P,Q,R): equivalence testing is
  rank-pruned backtracking + nullspace enumeration + an exact multiset
  check, ~ms per pair, returning a witness or a refutation.
- **`db_cse_screen.py`** — the full-database sweep: all 17,376 HKS
  schemes converted (0 parse failures; 13/13 byte-identical anchor
  controls) and CSE-screened.
- **`orbit_cse.py`** — hill-climbing over a scheme's de Groote orbit with
  the CSE count as objective; moves are single **transvections**
  (I + E_ij) on one of P/Q/R (dense local neighborhood; uniform-random
  group elements have ~0.06% acceptance and cannot fine-tune), plus
  plateau-walking and occasional random jumps.

**Calibrations.** Our optimizer reproduces the published frontier
head-to-head: Laderman → **62** (= Mårtensson–Wagner's record for that
scheme); Stapleton's representative with his signs → **60** exactly
(16+16+28). All counts in this note use 16 sign models × 96–128 restarts
unless stated.

## 3. Results

**The four record classes** (HKS DB identifiers; all pairwise
inequivalence claims are exact `equivalent()` refutations, 10/10 pairs
across the four 60-representatives and their sources):

| de Groote class | stored-rep CSE | best rep CSE (A+B+C) | 60-rep support | found by |
|---|---|---|---|---|
| `i2w201c26fi` (= Stapleton) | 62 | 60 (16+16+28) | 152 | his pipeline; reclassified here |
| `i106w191c347g` | 61 | **60 (15+16+29)** | 153 | DB screen + orbit climb |
| `i106w191c23ci` | 61 | **60 (16+15+29)** | 153 | orbit climb (1.4 s) |
| `i107w189c48ae` | 61 | **60 (15+16+29)** | 152 | orbit climb (15.2 s) |

**The full-DB screen** (2×6 effort per scheme, <2 minutes wall): exactly
three classes reach 61 from their stored representatives; nine reach 62;
the classics: Laderman 62, Smirnov 68 (sparsest ≠ most CSE-able). The
top of the leaderboard is committed (`matmul/cse_screen_top200.csv`).

**Non-invariance of the CSE count.** Sign/restart intensification
(16×96) does **not** move a stored representative below its plateau
(e.g. `i106w191c347g` holds at 61); the orbit move does (61 → 60), and
in Stapleton's class the gap between representatives is two additions
(62 vs 60). Notably the 60-representatives have *higher* support than
the 61-representatives they came from (144 → 153 nonzeros while 61 → 60
additions): naive sparsity and optimized additive cost are decoupled
axes, so weight-minimized databases are not addition-minimized.

**Our family's ceiling at 60.** For each of the four classes we ran
transvection-move orbit walks with plateau acceptance (15 min each;
20,740 / 23,770 / 23,567 / 22,885 proposals; 1,504 / 70 / 79 / 83
accepted moves), each accepted representative re-scored at high effort,
plus 16×128 sign×restart passes on every 60-representative. **No
configuration reached 59 anywhere.** Four independent classes
converging on exactly 60 looked like either a true barrier or a shared
heuristic ceiling; Perminov's 58 (published Dec 2025, after the
frontier this note was written against) settles it as the latter. The
measurement stands as a characterization of the greedy-CSE family; no
nontrivial additive lower bound is known for this setting.

## 4. Reclassification of Stapleton's scheme

Reconstructing the published SLP symbolically (`stapleton.py`; verified
mod 2 and exactly over ℤ; support 152, naive 97 — hence not Laderman's
form) and testing against the full database: exactly one fingerprint
collision, and the exact checker returns an equivalence witness to
**`i2w201c26fi-000`**. His discovery pipeline is genuinely interesting
(5.5 s end-to-end); but the *scheme* was in the 2019 database, and the
addition record should be read as: **Greedy-Potential applied to a
well-chosen representative of a known class** — which is also precisely
how our three additional 60s were produced, with the orbit search made
explicit and automated.

## 5. What is new here, plainly

- Three new record-count schemes on classes where no addition
  optimization had ever been published — tripling the number of known
  60-addition classes.
- The first (to our knowledge) full-database additive-complexity survey,
  and the observation that the record question factors as
  (class) × (orbit representative) × (signs) × (SLP heuristic), with the
  representative axis worth ≥2 additions and previously unsearched.
- An exact classification of the current record scheme.
- A negative with structure: 59 resists the entire greedy-family search
  across all four known record classes.

## 6. Reproduction

```bash
cd matmul
# calibrations (Laderman 62, Smirnov 68; ~1 min)
python3 slp.py --models 8 --restarts 24 seeds/laderman.bits seeds/smirnov.bits
# Stapleton: reconstruct + verify + classify + reproduce his 60  (~2 min)
python3 stapleton.py --models 16 --restarts 48
# the three schemes: confirm 60 at high effort (each line replay-verified)
python3 slp.py --models 16 --restarts 128 external/i106-orbitbest.bits \
    external/i106b-orbitbest.bits external/i107-orbitbest.bits
# pairwise inequivalence of the four
python3 - <<'EOF'
import sys; sys.path.insert(0, '.')
from equiv import load_schemes, equivalent
reps = [load_schemes([p])[0][1] for p in (
    'external/stapleton60.bits', 'external/i106-orbitbest.bits',
    'external/i106b-orbitbest.bits', 'external/i107-orbitbest.bits')]
print(all(not equivalent(reps[i], reps[j])
          for i in range(4) for j in range(i+1, 4)))
EOF
# the full-DB screen (downloads the DB once; ~20 min)
python3 dbcheck.py fetch convert && python3 db_cse_screen.py --workers 6
# emit a full SLP for any scheme
python3 slp.py --models 16 --restarts 128 \
    --emit /tmp/slp.txt external/i106-orbitbest.bits
```

Deterministic caveats: kissat may return different sign models across
versions (any returned model is then exactly verified); orbit climbs are
stochastic — the *committed representatives* make all headline claims
deterministic to check.

## 7. Limitations and the route to 59

All counts are upper bounds from one heuristic family; nothing here
bounds the optimum from below. Perminov's 58 shows what a stronger
pipeline (scheme search coupled to a stronger CSE) extracts; notably
his method searches schemes and subexpressions jointly — the same
(class × representative × signs × optimizer) factorization this note
makes explicit, with better optimization. The constructive combination
is open in both directions: classify his 58-scheme against the HKS
database with our exact machinery (as we did Stapleton's), and drive
his optimizer with our orbit/sign search axes — either could move 58.
Exact SLP minimization (SAT/ILP) on the output side (~29 additions in
all four of our 60s) remains the in-principle route to optimality
statements.

## References

- J. Stapleton. *A 60-Addition, Rank-23 Scheme for Exact 3×3 Matrix
  Multiplication.* arXiv:2508.03857 (2025).
- E. Mårtensson, P. S. Wagner. IACR ePrint 2024/2063 (Greedy-Potential;
  Laderman 98 → 62). Code: `werekorren/fmm_add_reduction`.
- O. Schwartz, N. Vaknin. *Pebbling Game and Alternative Basis for High
  Performance Matrix Multiplication.* SIAM J. Sci. Comput. 45(6), 2023.
- M. Heule, M. Kauers, J. Seidl. SAT 2019 + J. Symb. Comput. 104 (2021);
  scheme database: algebra.uni-linz.ac.at/research/matrix-multiplication.
- J. Laderman. Bull. AMS 82(1):126–128, 1976.
- H. F. de Groote. *On varieties of optimal algorithms for the
  computation of bilinear mappings.* Theor. Comput. Sci. 7 (1978).

## Appendix: a complete 60-addition program (class `i106w191c347g`)

Replay-verified; also on disk as `matmul/external/i106-60adds-slp.txt`
with the scheme bits at `matmul/external/i106-orbitbest.bits`.
Cost model: binary ± counted, unary negation free. A-side 15, B-side 16,
outputs 29 = **60 additions, 23 multiplications** (M_i = P_i · Q_i).

```text
## A-side: 15 additions
w0 = a22 + a32          w1 = a11 + a13          w2 = a23 + w0
w3 = a31 + w1           w4 = a21 + w1           w5 = a21 + w0
P1 = a33                P2 = w2                 P3 = w3
P4 = a23                P5 = a22 + a23          P6 = w4
P7 = a13                P8 = a12                P9 = w1
P10 = a33 + w2 + w3     P11 = a32               P12 = a31
P13 = w0                P14 = w5                P15 = a12
P16 = a11 + a31         P17 = a33               P18 = a31 + w5
P19 = a23 + w4          P20 = a21 + a22         P21 = a21
P22 = a11 + a12         P23 = a11 + a21

## B-side: 16 additions
w0 = b11 + b12          w1 = b21 + b22          w2 = b13 - b23
w3 = b32 - w1           w4 = b32 - w0           w5 = b11 - w2
Q1 = b31                Q2 = -w3                Q3 = -w4
Q4 = -b31 + b33 - w3    Q5 = w1                 Q6 = -b33 + w0
Q7 = -b31 - w4          Q8 = w1                 Q9 = w0
Q10 = b32               Q11 = b21               Q12 = b11
Q13 = b22 - b32 + w5    Q14 = w5                Q15 = b22
Q16 = b12 - b32         Q17 = b33               Q18 = b11 - b13
Q19 = b33               Q20 = b23               Q21 = w0 - w2
Q22 = b23               Q23 = -b33 + w2

## outputs: 29 additions
w0 = M12 - M3           w1 = M21 - M6           w2 = M9 + w1
w3 = M2 - M11           w4 = M15 + M16          w5 = w0 + w4
w6 = M13 - M14          w7 = M19 - w2           w8 = w3 - w6
C11 = -M7 + M8 - w5     C12 = M9 + w5           C13 = M22 + M23 + w2
C21 = -M4 + w7 + w8     C22 = M21 + M5 - w8     C23 = M20 + w7
C31 = M1 + M11 + M12    C32 = -M5 - M9 + M10 - w0 + w3
C33 = M12 + M14 + M17 - M18 - M20
```
