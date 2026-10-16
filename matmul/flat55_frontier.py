#!/usr/bin/env python3
"""Build the fat-55 frontier list for the exact flat-total check, and
summarize its results.

  build   cfloor.log all_schemes.txt out.list
          -- every scheme with some slot reaching GF(2) output side 27
             (cfloor 'FAT55' lines), as 'name bits' lines for
             floors --list
  report  floors.log
          -- histogram of exact orbit-wide GF(2) flat minima; lists
             every class at <= 55

Classes OUTSIDE the frontier cannot host a flat 55 except through
sides <= 27, which the July exhaustive slim-sides analysis covered
(only the record class i19w225c4efh reaches 55 there); so frontier +
that analysis decide flat-55 uniqueness for the whole database.
"""
import re
import sys
from collections import Counter

mode = sys.argv[1]
if mode == "build":
    log, allf, out = sys.argv[2:5]
    names = []
    for ln in open(log):
        m = re.match(r"FAT55 (\S+) slot", ln)
        if m and m.group(1) not in names:
            names.append(m.group(1))
    want = set(names)
    bits = {}
    for ln in open(allf):
        parts = ln.split()
        if len(parts) == 2 and parts[0] in want:
            bits[parts[0]] = parts[1]
    missing = want - set(bits)
    with open(out, "w") as f:
        for n in names:
            if n in bits:
                f.write(f"{n} {bits[n]}\n")
    print(f"frontier: {len(names)} schemes ({len(missing)} missing bits) -> {out}")
elif mode == "report":
    mins = {}
    for ln in open(sys.argv[2]):
        m = re.match(r"(\S+) v\d+ EXACT-TOTAL min=(\d+)", ln)
        if m:
            name, v = m.group(1), int(m.group(2))
            mins[name] = min(v, mins.get(name, 10 ** 9))
    hist = Counter(mins.values())
    print(f"classes checked: {len(mins)}")
    for v in sorted(hist):
        print(f"  flat min {v}: {hist[v]}")
    low = sorted((v, n) for n, v in mins.items() if v <= 55)
    print(f"at <= 55: {len(low)}")
    for v, n in low:
        print(f"  {n}: {v}")
