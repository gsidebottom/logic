#!/usr/bin/env python3
"""Render doc/matmul_53_3x3_schemes.md as a typeset PDF: display math via
matplotlib mathtext (STIX), body text in reportlab with STIX fonts so
Greek/math glyphs render, subscripts as real subscripts."""
import io
import os
import re

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import font_manager
from reportlab.lib import colors
from reportlab.lib.enums import TA_JUSTIFY
from reportlab.lib.pagesizes import letter
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.units import inch
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (Image, PageBreak, Paragraph,
                                Preformatted, SimpleDocTemplate, Spacer,
                                Table, TableStyle)

ROOT = "/Users/greg/projects/logic"
OUT = f"{ROOT}/doc/matmul_53_3x3_schemes.pdf"

# ---- fonts: STIX ships with matplotlib ----
ttf_dir = os.path.join(os.path.dirname(matplotlib.__file__),
                       "mpl-data", "fonts", "ttf")
pdfmetrics.registerFont(TTFont("STIX", f"{ttf_dir}/STIXGeneral.ttf"))
pdfmetrics.registerFont(TTFont("STIX-B", f"{ttf_dir}/STIXGeneralBol.ttf"))
pdfmetrics.registerFont(TTFont("STIX-I", f"{ttf_dir}/STIXGeneralItalic.ttf"))
pdfmetrics.registerFontFamily("STIX", normal="STIX", bold="STIX-B",
                              italic="STIX-I", boldItalic="STIX-B")
MONO = "Courier"

BODY = ParagraphStyle("body", fontName="STIX", fontSize=10.2, leading=13.6,
                      alignment=TA_JUSTIFY, spaceAfter=5)
H1 = ParagraphStyle("h1", fontName="STIX-B", fontSize=16, leading=20,
                    spaceBefore=8, spaceAfter=8)
H2 = ParagraphStyle("h2", fontName="STIX-B", fontSize=12.5, leading=16,
                    spaceBefore=12, spaceAfter=5,
                    textColor=colors.HexColor("#1a3a5c"))
H3 = ParagraphStyle("h3", fontName="STIX-B", fontSize=10.8, leading=14,
                    spaceBefore=8, spaceAfter=4,
                    textColor=colors.HexColor("#2c5170"))
META = ParagraphStyle("meta", fontName="STIX-I", fontSize=9.5, leading=13,
                      textColor=colors.HexColor("#555555"), spaceAfter=4)
CODE = ParagraphStyle("code", fontName=MONO, fontSize=7.6, leading=9.6,
                      backColor=colors.HexColor("#f4f4f4"),
                      borderPadding=6, spaceBefore=4, spaceAfter=6)
LIST = ParagraphStyle("list", parent=BODY, leftIndent=16,
                      bulletIndent=6, spaceAfter=3)

def mathimg(tex, fontsize=13):
    """render mathtext -> tight high-res PNG, sized in points."""
    fig = plt.figure()
    fig.text(0.5, 0.5, tex, fontsize=fontsize, math_fontfamily="stix",
             ha="center", va="center")
    buf = io.BytesIO()
    fig.savefig(buf, format="png", dpi=300, transparent=True,
                bbox_inches="tight", pad_inches=0.03)
    plt.close(fig)
    buf.seek(0)
    from PIL import Image as PILImage
    w_px, h_px = PILImage.open(buf).size
    buf.seek(0)
    return Image(buf, width=w_px / 300 * 72, height=h_px / 300 * 72)


def centered(img):
    t = Table([[img]], colWidths=[6.6 * inch])
    t.setStyle(TableStyle([("ALIGN", (0, 0), (-1, -1), "CENTER")]))
    return t

def P(txt, style=BODY):
    return Paragraph(txt, style)

story = []
story.append(P("53 New Integer Schemes for 3×3 Matrix Multiplication "
               "with 23 Products", H1))
story.append(P("Reproducible report — logic repo, matmul track, "
               "2026-07-03 (commits 45e5acc…93347f2). All artifacts live "
               "in the repository; every claim has a mechanical check "
               "(§4). Canonical source: doc/matmul_53_3x3_schemes.md.",
               META))
story.append(Spacer(1, 6))

story.append(P("1. Summary", H2))
story.append(P("We report <b>53 new schemes for multiplying two 3×3 "
               "matrices with 23 multiplications, with coefficients in "
               "{−1, 0, +1}</b> — valid over any commutative ring, the "
               "same object class as Laderman's 1976 scheme. Each scheme "
               "is:"))
for i, s in enumerate([
    "<b>verified mod 2</b> against all 729 Brent equations,",
    "<b>pairwise inequivalent</b> under the full de Groote symmetry "
    "group GL(3,2)<super>3</super> ⋊ S<sub>3</sub> (exact "
    "witness-or-refutation checks),",
    "<b>inequivalent to every published scheme</b>: all 17,376 schemes "
    "of the Kauers–Heule–Seidl (HKS) database <i>and</i> the four "
    "classics (Laderman 1976, Smirnov 2013, Oh–Kim–Moon 2013, "
    "Courtois–Bard–Hulme 2011),",
    "<b>lifted to integer coefficients</b> in {−1,0,+1} and verified "
    "<b>exactly over ℤ</b> against all 729 integer Brent equations."]):
    story.append(P(f"{i+1}.  {s}", LIST))
story.append(P(
    "Discovery cost: the 53 came out of one <b>6-minute single-threaded "
    "run</b> of a neighborhood-walk pipeline (138 raw finds → 53 "
    "survived full-database novelty checking), plus ≈40 minutes of "
    "certification compute. For scale: the HKS campaign that produced "
    "the 17,376-scheme database used ≈35 CPU-years (methods differ; §7)."))
story.append(P(
    "The engine is a <b>native-ANF stochastic local search</b>: the "
    "Brent system is kept as 729 cubic-XOR constraints over the 621 "
    "real variables instead of a ≈26,500-variable CNF, which extends "
    "the seeded-repair horizon by ≥5,000× over yalsat-on-CNF and, with "
    "an exact GF(2) tensor-closure move, solves 8/10 of the official "
    "HKS challenge-1 instances (yalsat's published record: 5/10)."))

story.append(P("2. Background", H2))
story.append(P(
    "A bilinear scheme for 3×3 matrix multiplication with r products is "
    "a triple of coefficient tensors α, β, γ:"))
story.append(centered(mathimg(
    r"$M_m=\left(\sum_{a,b}\alpha^{(m)}_{ab}A_{ab}\right)"
    r"\left(\sum_{c,d}\beta^{(m)}_{cd}B_{cd}\right),\qquad "
    r"C_{pq}=\sum_{m=1}^{r}\gamma^{(m)}_{pq}\,M_m$")))
story.append(P("Correctness is equivalent to the <b>Brent equations</b>; "
               "over GF(2):"))
story.append(centered(mathimg(
    r"$\bigoplus_{m=1}^{r}\ \alpha^{(m)}_{ab}\,\beta^{(m)}_{cd}\,"
    r"\gamma^{(m)}_{pq}\;=\;\delta_{bc}\,\delta_{ap}\,\delta_{dq}"
    r"\qquad\forall\,(a,b,c,d,p,q)\in[3]^6$")))
story.append(P(
    "i.e. 729 cubic XOR equations over 27r variables (r = 23: 621 "
    "variables; 27 equations have right-hand side 1 — the “type-3” or "
    "delta equations). Any integer scheme reduces mod 2 to a GF(2) "
    "scheme; conversely a GF(2) scheme <i>may</i> lift to signs ±1 (HKS "
    "observe lifting rarely fails)."))
story.append(P(
    "Known landscape: r = 23 achievable (Laderman 1976); best lower "
    "bound 19 (Bläser 2003); <b>r = 22 open in both directions</b>. "
    "Before HKS (SAT 2019 / J. Symbolic Computation 2021), only 4 "
    "inequivalent {−1,0,1} schemes were known; their local-search "
    "campaign found &gt;17,000 more, all published in the Linz database "
    "this report checks against."))

story.append(P("3. The pipeline", H2))
story.append(P("3.1  Native-ANF SLS engine (src/anf.rs, binary anf)", H3))
story.append(P(
    "The Brent system is represented natively as cubic-XOR (ANF) "
    "constraints — no Tseitin auxiliaries. Flipping a variable touches "
    "exactly its 81 incident equations; a monomial toggles iff its two "
    "partner bits are 1, so incremental evaluation is O(81) per flip "
    "(0.4–5 M flips/s/core measured; ≈10 M flips/s aggregate over 10 "
    "threads). Two policy regimes: close repair (WalkSAT/SKC, noise "
    "0.2, init density 0.25) and pairing/from-scratch (probSAT, "
    "c<sub>b</sub> = 2.5, init density 0.10 ≈ the free-support density "
    "of real completions)."))
story.append(P(
    "The structural move is the <b>tensor closure</b>: the system is "
    "tri-linear and every equation contains exactly one variable-group "
    "of each tensor, so fixing two tensors decomposes the third into 9 "
    "independent 81×r GF(2) linear systems — a consistent single-tensor "
    "closure <i>solves the instance outright</i>, and each closure call "
    "is monotone. It runs as an injected hook every N flips."))
story.append(P(
    "Baselines (this machine): kissat cannot solve the r = 23 CNF "
    "(unknown at 60 s; 41.6 s to prove even 2×2-in-6 UNSAT). yalsat "
    "(HKS's solver, v1.0.1) matches its published seeded operating "
    "point (fix 414/621 bits: 0.05–0.2 s) but <b>times out at 300 s at "
    "fix = 300 and fix = 250 — instances the native engine solves in "
    "5 ms and 60 ms</b>. On the official challenge-1 instances the "
    "native engine + closure solves <b>8/10</b> (best 0.019 s / "
    "0.069 s; the latter confirmed by planting our bits into "
    "<i>their</i> CNF and running kissat: SATISFIABLE)."))
story.append(P("3.2  Discovery: neighborhood walk (matmul/walk.py)", H3))
story.append(P(
    "HKS “method 2,” compounding: a pool of 24 verified seeds (4 "
    "classics + 20 spanning 20 DB rank-pattern directories); each hop "
    "freezes a random 300 of a pool scheme's 621 bits and lets the "
    "engine complete the rest; completions are canon-deduped (sorted "
    "summands); genuinely new schemes join the pool. Every accepted "
    "scheme is re-verified by code independent of the search. The "
    "committed run: <b>138 schemes at ≈3 s/scheme</b>, accelerating as "
    "the pool diversifies."))
story.append(P("3.3  Exact equivalence (matmul/equiv.py)", H3))
story.append(P(
    "“New” must mean new modulo de Groote symmetry. Writing schemes as "
    "summands (A, B, C̃) with C̃ = γ<super>T</super>, the group acts as "
    "the cyclic sandwich"))
story.append(centered(mathimg(
    r"$(A,B,\tilde{C})\ \mapsto\ (P\,A\,Q^{-1},\ Q\,B\,R^{-1},\ "
    r"R\,\tilde{C}\,P^{-1}),\qquad G=\mathrm{GL}(3,2)^3\rtimes S_3,"
    r"\quad |G|=168^3\cdot 6$")))
story.append(P(
    "so every summand-matching constraint is <b>linear</b> in the 27 "
    "GF(2) unknowns of (P, Q, R): equivalence testing is rank-pruned "
    "backtracking + incremental RREF + nullspace enumeration + an exact "
    "multiset check (≈ms per pair), returning a witness or a "
    "refutation. Self-tests: 12 random group elements recovered "
    "equivalent-with-witness; Laderman vs Smirnov refuted. On the 138 "
    "finds: <b>129 distinct classes</b>."))
story.append(P("3.4  Database novelty (matmul/novelty.py, dbcheck.py)", H3))
story.append(P(
    "Layer 1 — rank-pattern absence: the DB's 302 directory names "
    "encode per-summand rank types (legend constraint-solved from 20 "
    "known dir↔scheme pairs); rank patterns are G-invariants, so "
    "pattern-absence ⇒ inequivalence. Control: Laderman's pattern is "
    "absent from all 302 found-scheme directories — correct. Layer 2 — "
    "full-database exact check: all <b>17,376</b> schemes fetched "
    "(schemes.tgz), converted with 0 parse failures and 13/13 "
    "byte-identical anchors; per find, fingerprint filtering then exact "
    "equivalence. Hardening: all 17,376 fingerprinted; the surviving "
    "finds (×6 S<sub>3</sub> variants) have <b>zero fingerprint matches "
    "anywhere</b> — verdicts independent of the directory-name legend. "
    "Result: 85 finds equivalent to DB schemes (walk is DB-seeded; "
    "witnesses recorded), <b>53 new vs the entire database</b>, "
    "pairwise inequivalent, inequivalent to the classics."))
story.append(P("3.5  Integer lifting (matmul/lift.py)", H3))
story.append(P(
    "Lifting as <b>sign-SAT</b> (vs HKS's Gröbner route): one sign bit "
    "per support coefficient; a covering term's sign is the XOR of its "
    "three sign bits; the integer Brent equation with k covering terms "
    "and right-hand side δ becomes “exactly (k−δ)/2 of the k term-bits "
    "equal 1”; per-product scaling is broken by fixing the first α- and "
    "β-support signs. ≈2,000-clause CNFs, kissat solves each in "
    "milliseconds; every lift is verified <b>exactly over ℤ</b> by "
    "independent code. Controls: all 4 classics lift. Result: "
    "<b>53/53 lifted, zero failures</b> (matmul/lifted/*.txt)."))

story.append(PageBreak())
story.append(P("4. Verification chain — check every claim", H2))
story.append(Preformatted(
"""# 0. build + engine self-tests                                [~1 min]
cargo build --release --bin anf
cargo test --release --lib anf::          # expect: 7 passed

# 1. generator sanity (Strassen + Laderman verify)              [~5 s]
cd matmul && python3 brent.py selftest

# 2. the 53 are valid + distinct-after-sorting                  [~10 s]
grep NEW novelty_verdicts.csv | cut -d, -f1 | sed 's|^|found/|;s|$|.bits|' \\
  | xargs cat | python3 canon.py 3 3 3 23 /dev/stdin
#   expect: 53 schemes read, 0 INVALID, 53 distinct after summand sorting

# 3. exact-equivalence self-test + 53 = 53 classes              [~30 s]
python3 equiv.py selftest
grep NEW novelty_verdicts.csv | cut -d, -f1 | sed 's|^|found/|;s|$|.bits|' \\
  | xargs python3 equiv.py classes      # expect: TOTAL de-Groote classes: 53

# 4. rank-pattern novelty vs the 302 DB dirs (no download)      [~30 s]
python3 novelty.py db_rank_patterns.txt found/walk-00029.bits

# 5. FULL database check from primary sources                   [~15 min]
python3 dbcheck.py all
#   fetch (43 MB) -> convert 17,376 (expect 0 failures) -> controls
#   (20 byte-identical seeds + 4 classics) -> check vs ALL fingerprints;
#   ends with cross-check vs committed novelty_verdicts.csv: MATCH

# 6. integer lifting + exact Z-verification                     [~1 min]
grep NEW novelty_verdicts.csv | cut -d, -f1 | sed 's|^|found/|;s|$|.bits|' \\
  | xargs python3 lift.py --outdir /tmp/lift53
#   expect: "53 lifted, 0 not +-1-liftable"; each line Z-VERIFIED

# 7. challenge-1 spot-check (their exact CNF, our scheme)       [~1 min]
git clone https://github.com/marijnheule/matrix-challenges challenges
mkdir -p inst && python3 import_core.py \\
  challenges/challenge1/MM-23-2-2-2-2-A.cnf inst/core-A.freeze
../target/release/anf 3 3 3 23 --freeze-file inst/core-A.freeze \\
  --probsat --cb 2.5 --density 0.1 --seconds 60 --threads 10 --seed 3 \\
  --quiet | grep '^b ' > /tmp/solA.txt
python3 check_their_cnf.py challenges/challenge1/MM-23-2-2-2-2-A.cnf \\
  /tmp/solA.txt                      # expect: SATISFIED by our scheme""",
    CODE))
story.append(P(
    "Verification of the committed 53 (steps 0–6) is deterministic. "
    "Discovery (walk.py) and the challenge-1 solves are stochastic and "
    "timing-dependent: reruns reproduce the phenomena, not "
    "bit-identical artifacts. kissat may return different sign models "
    "across versions — any model returned is then ℤ-verified, which is "
    "the claim that matters."))

story.append(P("5. The 53 schemes", H2))
story.append(P(
    "Files: mod-2 bit-vectors matmul/found/walk-*.bits (the 53 names "
    "are the NEW rows of matmul/novelty_verdicts.csv); signed integer "
    "forms matmul/lifted/walk-*.txt. Support = number of nonzero "
    "coefficients; for a 3×3×23 scheme the naive addition count is "
    "exactly support − 55. Ours: support 149–164 (median 154) = "
    "<b>94–109 naive additions</b>; reference points: Laderman 153/98, "
    "Smirnov 139/84 = the DB minimum (support percentiles of the full "
    "DB: p1 = 146, median = 159 — our sparsest sits at the 3rd "
    "percentile; 22 of the 53 need fewer naive additions than "
    "Laderman; none beats the DB's sparsest). Rank-type multiset = "
    "per-summand sorted (rank α, rank β, rank γ) with multiplicities — "
    "the invariant separating 51 of the 53 from the whole DB at the "
    "coarsest level."))
story.append(Spacer(1, 4))

# ---- the 53-row table, parsed from the markdown source ----
md = open(f"{ROOT}/doc/matmul_53_3x3_schemes.md").read()
rows = re.findall(r"\| (walk-\d+) \| (\d+) \| ([0-9× ]+) \|", md)
assert len(rows) == 53, f"expected 53 rows, got {len(rows)}"
tdata = [["scheme", "support", "naive adds", "rank-type multiset"]]
for name, sup, pat in rows:
    tdata.append([name, sup, str(int(sup) - 55), pat.strip()])
tbl = Table(tdata, colWidths=[1.15 * inch, 0.7 * inch, 0.85 * inch,
                              3.6 * inch], repeatRows=1)
tbl.setStyle(TableStyle([
    ("FONTNAME", (0, 0), (-1, 0), "STIX-B"),
    ("FONTNAME", (0, 1), (-1, -1), MONO),
    ("FONTSIZE", (0, 0), (-1, 0), 8.5),
    ("FONTSIZE", (0, 1), (-1, -1), 7.4),
    ("LINEBELOW", (0, 0), (-1, 0), 0.8, colors.HexColor("#1a3a5c")),
    ("ROWBACKGROUNDS", (0, 1), (-1, -1),
     [colors.white, colors.HexColor("#f0f3f6")]),
    ("TOPPADDING", (0, 0), (-1, -1), 1.6),
    ("BOTTOMPADDING", (0, 0), (-1, -1), 1.6),
]))
story.append(tbl)
story.append(P(
    "<i>The multiset shown is the coarse invariant; schemes sharing it "
    "are separated by the finer pair-sum fingerprint and/or exact "
    "checks. All 53 are pairwise inequivalent.</i>", META))

story.append(P("6. Secondary results", H2))
for s in [
    "<b>Challenge 1 (HKS): 8/10 official instances solved</b> (pairing "
    "cores, no streamliners; yalsat's record 5/10). The two holdouts "
    "floor at best 3/729 after 600 s × 10 threads.",
    "<b>Path-space SLS (local search on the connection method): built, "
    "verified correct, measured NEGATIVE</b> at equal budget vs "
    "assignment-space SLS. Diagnosis: the connection objective "
    "collapses (a conflicted variable hides force1×force0 repairs) and "
    "the Brent matrix's sharing is dense (81 equations/variable) — "
    "path rerouting is myopic exactly where one assignment flip "
    "re-evaluates everything at once.",
    "<b>r = 22 (challenge 4): open, probed.</b> Plain native attacks "
    "floor at 8/729; drop-a-product repairs floor at 1/729, but the "
    "finisher proved every such floor-1 state violates exactly the "
    "type-3 equation whose sole cover was dropped and is rigid to "
    "radius 3 — the floor-1 shell is a seeding artifact, not evidence "
    "about r = 22."]:
    story.append(P("•  " + s, LIST))

story.append(P("7. Caveats and scope", H2))
for s in [
    "“New” = inequivalent under de Groote symmetry to the 17,376 "
    "schemes of the Linz database snapshot (schemes.tgz, 2020-08-07) "
    "and the 4 classics. No claim about unpublished or post-2020 "
    "collections.",
    "Discovery-effort comparisons with HKS (35 CPU-years vs minutes) "
    "are indicative, not controlled: we start from their published "
    "schemes; they started from 4 and invented the methods. The "
    "like-for-like numbers are the same-machine yalsat A/Bs (§3.1).",
    "The checkers are our code; self-tests and controls are listed in "
    "§4. Strongest external anchors: our challenge-1 solution "
    "satisfies HKS's own CNF under kissat, and the DB hardening uses "
    "only rank arithmetic + the exact checker on published inputs.",
    "51/53 schemes have four rank-(2,2,2) summands (like most HKS "
    "finds); none matches Laderman's four-quadruple core type."]:
    story.append(P("•  " + s, LIST))

story.append(P("8. Pointers", H2))
story.append(P(
    "Lab notebook: doc/matmul_plan.md (every measurement, including "
    "negatives and retractions). Engine: src/anf.rs, src/bin/anf.rs. "
    "Tools: matmul/{brent, sls, walk, canon, equiv, novelty, dbcheck, "
    "lift, import_core, check_their_cnf}.py. External sources fetched "
    "by commands shown in §4: the DB archive, the matrix-challenges "
    "clone, yalsat. References: HKS SAT 2019 (arXiv:1903.11391) and "
    "J. Symb. Comput. 104 (2021); Laderman, Bull. AMS 82(1), 1976; "
    "Bläser, J. Complexity 19(1), 2003; database: "
    "algebra.uni-linz.ac.at/research/matrix-multiplication."))

doc = SimpleDocTemplate(OUT, pagesize=letter,
                        leftMargin=0.9 * inch, rightMargin=0.9 * inch,
                        topMargin=0.8 * inch, bottomMargin=0.8 * inch,
                        title="53 New Integer Schemes for 3x3 Matrix "
                              "Multiplication with 23 Products")
doc.build(story)
print("wrote", OUT, os.path.getsize(OUT), "bytes")
