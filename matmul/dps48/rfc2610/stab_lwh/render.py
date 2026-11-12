#!/usr/bin/env python3
"""Render stabilizer elements as plain text for the letter's attachment (Lemma 2.1 form).
  render.py KIND IN.json OUT.txt TITLE     KIND = qt (entries Laurent in t) or num (iso_between output)"""
import json, sys
from fractions import Fraction

def show(p):
    """Laurent polynomial {exponent: coefficient} as text, e.g. 1 - 1/4*t^(-1), -4*t + 1"""
    if not p:
        return "0"
    out = ""
    for e in sorted(p, reverse=True):
        c = p[e]
        mon = "" if e == 0 else ("t" if e == 1 else f"t^{e}" if e > 0 else f"t^({e})")
        cs = str(abs(c))
        term = cs if not mon else (mon if abs(c) == 1 else f"{cs}*{mon}")
        out += ((" - " if c < 0 else " + ") + term) if out else (("-" if c < 0 else "") + term)
    return out

def cycles(pi):
    seen, out = set(), []
    for k in range(48):
        if k in seen:
            continue
        c, j = [], k
        while j not in seen:
            seen.add(j); c.append(j + 1); j = pi[j]
        if len(c) > 1:
            out.append("(" + ",".join(map(str, c)) + ")")
    return "".join(out) or "()"

def table(M):
    w = max(len(x) for r in M for x in r)
    return ["    [ " + "  ".join(x.rjust(w) for x in r) + " ]" for r in M]

kind, src, dst, title = sys.argv[1:5]
els = json.load(open(src))
if kind == "qt":
    for e in els:
        e["text"] = {m: [[show({int(k): Fraction(v) for k, v in p.items()}) for p in r] for r in e[m]] for m in "XYZUVW" if m in e}
    json.dump(els, open(dst.replace(".txt", ".json"), "w"), indent=0)
lines = [title, "=" * len(title), f"{len(els)} elements", ""]
for n, e in enumerate(els, 1):
    lines.append(f"element {n}:  map {e['act']}")
    lines.append(f"  perm {cycles(e['pi'])}")
    for m in "UVW":
        if kind == "qt":
            M = [[show({int(k): Fraction(v) for k, v in p.items()}) for p in r] for r in e[m]]
        else:
            M = [[str(x) for x in r] for r in e[m]]
        lines.append(f"  {m} =")
        lines += table(M)
    lines.append("")
open(dst, "w").write("\n".join(lines) + "\n")
print(f"{dst}: {len(els)} elements")
