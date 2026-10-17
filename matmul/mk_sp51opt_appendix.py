#!/usr/bin/env python3
"""Extract Appendix B of the KS-51 paper from proof/Mm/SP51Optimal.lean:
the definitions IsChain, Computable, ComputableFromBasis and the statement
of kernel_optimal_for_class, verbatim, typeset for an alltt environment
(Lean's Unicode symbols become math symbols, with \\sb for subscripts since
alltt makes `_` literal; braces are escaped).  Writes
doc/matmul_3x3_rank23_add51_appendixB.tex for \\input.

Usage: mk_sp51opt_appendix.py [SP51Optimal.lean] [appendixB.tex]
"""
import pathlib
import sys

SRC = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "proof/Mm/SP51Optimal.lean")
DST = pathlib.Path(sys.argv[2] if len(sys.argv) > 2
                   else "doc/matmul_3x3_rank23_add51_appendixB.tex")
lines = SRC.read_text().splitlines()


def block(head, stop_at_by=False):
    i = next(k for k, ln in enumerate(lines) if ln.startswith(head))
    out = []
    for ln in lines[i:]:
        if stop_at_by and ln.rstrip().endswith(":= by"):
            out.append(ln.rstrip()[: -len(":= by")].rstrip())
            break
        if not ln.strip():
            break
        out.append(ln)
    return out


parts = [block("def IsChain"), block("def Computable (T"), block("def ComputableFromBasis"),
         block("theorem kernel_optimal_for_class", stop_at_by=True)]
text = "\n\n".join("\n".join(p) for p in parts)

text = text.replace("\\", "\\(\\backslash\\)").replace("{", "\\{").replace("}", "\\}")
MATH = {"ℕ": r"\(\mathbb{N}\)", "→": r"\(\to\)", "∀": r"\(\forall\)", "∃": r"\(\exists\)",
        "∧": r"\(\land\)", "∨": r"\(\lor\)", "≤": r"\(\le\)", "∈": r"\(\in\)",
        "≃ₗ": r"\(\simeq\sb{l}\)"}
for k, v in MATH.items():
    text = text.replace(k, v)
bad = sorted({c for c in text if not (32 <= ord(c) < 127 or c == "\n")})
assert not bad, f"unmapped non-ASCII characters: {bad}"

DST.write_text("\\begin{alltt}\n" + text + "\n\\end{alltt}\n")
print(f"wrote {DST} ({text.count(chr(10)) + 1} lines) from {SRC}")
