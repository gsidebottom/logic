#!/usr/bin/env python3
"""Extract the paper appendix from proof/Mm/Ring51.lean: the scheme
definition and the matrix-product theorem, verbatim except for
ASCII-folding the typographic characters (the repository file stays
authoritative; the paper says so).  Writes
doc/matmul_3x3_rank23_add51_appendix.txt for \\verbatiminput.

Usage: mk_ks51_appendix.py [Ring51.lean] [appendix.txt]
"""
import pathlib
import sys

SRC = pathlib.Path(sys.argv[1] if len(sys.argv) > 1 else "proof/Mm/Ring51.lean")
DST = pathlib.Path(sys.argv[2] if len(sys.argv) > 2
                   else "doc/matmul_3x3_rank23_add51_appendix.txt")

lines = SRC.read_text().splitlines()
start = next(i for i, ln in enumerate(lines)
             if ln.startswith("/-- The 51-addition-per-step scheme as a map"))
end = next(i for i, ln in enumerate(lines) if ln == "end Ring51")
body = "\n".join(lines[start:end]).rstrip() + "\n"

FOLD = {"×": "x", "−": "-", "–": "-", "—": "--", "·": ".",
        "ℤ": "Z", "⟨": "<", "⟩": ">", "≤": "<=", "≥": ">="}
for k, v in FOLD.items():
    body = body.replace(k, v)
bad = sorted({c for c in body if not (32 <= ord(c) < 127 or c == "\n")})
assert not bad, f"unfolded non-ASCII characters: {bad}"

DST.write_text(body)
print(f"wrote {DST} ({len(body.splitlines())} lines) from {SRC}")
