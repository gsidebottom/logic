# arXiv submission kit — KS-51 and 55-addition papers

Source packages (built from the committed sources; `arxiv-upload/` is
gitignored): `arxiv-upload/arxiv-ks51-source.tar.gz` (main file plus its
two `\input` files) and `arxiv-upload/arxiv-mm55-source.tar.gz` (one
file).  Both sources are pure ASCII with standard packages, so arXiv's
pdflatex should compile them; check its PDF preview before submitting.

Common choices: license **arXiv.org perpetual, non-exclusive license**;
primary **cs.DS**, cross-lists **cs.SC**, **cs.CC** (Greg is endorsed in
cs, which arXiv treats as one endorsement domain).

## 1. KS-51 paper

**Title:** 51 Additions per Recursive Step for Rank-23 $3\times3$ Matrix
Multiplication, Machine-Checked over Arbitrary Rings

**Authors:** Greg Sidebottom

**Abstract:**

We present a rank-23 bilinear scheme for $3\times3$ matrix multiplication that uses 51 additions per recursive step in the alternative-basis (Karstadt-Schwartz) cost model, one below Nielsen's 52 (arXiv:2609.06588). The count 51 itself was first posted, on a different scheme, by Stapleton and Perminov (arXiv:2609.32388), found by heuristic sparse-basis search; the present work is independent and complementary: exactness and breadth rather than a single construction. The scheme is valid over every ring, so it recurses on block matrices, and its correctness is machine-checked in Lean 4/Mathlib. The count is exactly optimal for the scheme's equivalence class: we introduce an exact free-basis minimization procedure whose negative answers are exhaustion proofs, and use it to show that 51 is the minimum for this class, that 52 is exactly optimal both for Nielsen's class and for the class of the current flat-model record, and to sweep the complete Heule-Kauers-Seidl database of rank-23 classes. The sweep is complete: exactly four classes attain 51, all in a single HKS invariant family. We machine-check Stapleton and Perminov's scheme as well, and prove in Lean that their 51 is optimal for its class. Separately, we document a systematic gap between $\mathbb{F}_2$ and signed optima: the $\mathbb{F}_2$-optimal chains of a class typically admit no sign assignment under most of the class's integer sign models, and certificate lifting fails where a direct signed search succeeds.

**Comments:** 14 pages, 2 tables. Artifacts (certificates, exact
searcher, Lean 4 proofs): https://doi.org/10.5281/zenodo.23305910;
source: https://github.com/gsidebottom/logic

**MSC class:** 68W30, 68Q25, 15A69, 68V15
**ACM class:** F.2.1; I.1.2

## 2. 55-addition paper

**Title:** A 55-Addition Rank-23 Scheme for $3\times3$ Matrix
Multiplication via Exact Two-Sided Minimization

**Authors:** Greg Sidebottom

**Abstract:**

We multiply two $3\times3$ matrices with 23 multiplications and 55 additions, one below the previous record of 56 (Sun, arXiv:2604.27645): the first sub-56 scheme for exact non-commutative $3\times3$ multiplication without change of basis (Zenodo deposit of July 7, 2026; independently rediscovered by Karunaratne and Idamekorala, arXiv:2607.28676). The program forms 13 signed combinations of the entries of A and 14 of B, takes 23 products, and recombines them with 28 further additions. It is checked against the naive algorithm on random integer and non-commutative block inputs, so it holds over any ring and recurses on block matrices, and its correctness is machine-checked in Lean 4. The previous records, 60 down to 56, all came from greedy common-subexpression elimination, which only bounds each side of a scheme from above. We minimize both input sides exactly by chain covering, and the output side exactly via the transposition principle: the 9-by-23 output map costs its transpose plus 14, and the transpose is a 9-input map that the input-side minimizer solves exactly. On Perminov's cn122 scheme (class i19w225c4efh, published at 58) this gives 55 = 13 + 14 + 28, where greedy elimination reaches only 29 on the output side. The same method confirms that Sun's representative is output-optimal at 56. An exact orbit-wide computation over the Heule-Kauers-Seidl database shows that the record class is the only database class attaining 55, and that Sun's 56 and Perminov's cn119 56 are each exactly optimal for their class.

**Comments:** 11 pages. Artifacts (program, verifier, Lean 4 proof):
https://doi.org/10.5281/zenodo.21240904; source:
https://github.com/gsidebottom/logic

**MSC class:** 68W30, 68Q25, 15A69
**ACM class:** F.2.1; I.1.2
