#!/usr/bin/env python3
"""Compare the FLAG lines of kron_rank_scan logs with the catalog's best ranks.
usage: kron_flags_vs_best.py STATUS_JSON LOG [LOG ...]
A flag whose bound is below the best rank the catalog records for that shape (in the ring the flag holds
in) is a candidate record and is printed first.
"""
import sys, json, re
status = json.load(open(sys.argv[1]))
FL = re.compile(r'^FLAG (Q |F2) (\S+): \((\d+), (\d+), (\d+)\) m=(\d+): .*?-> at most (\d+) products(.*)$')
best = {}
for key, v in status.items():
    if isinstance(v, dict) and 'ranks' in v:
        best[key] = v['ranks']
rows = []
for log in sys.argv[2:]:
    for line in open(log, errors='replace'):
        m = FL.match(line.rstrip('\n'))
        if not m: continue
        ring, path, a, b, c, mm, bound, rest = m.groups()
        dims = sorted((int(a), int(b), int(c)))
        key = 'x'.join(map(str, dims))
        rk = best.get(key)
        rows.append((ring.strip(), key, int(mm), int(bound), rk, path, rest))
print(f'{len(rows)} flags; status has {len(best)} shapes')
cand = []
for ring, key, mm, bound, rk, path, rest in sorted(rows, key=lambda r: (r[1], r[0], r[2])):
    if rk is None:
        tag = 'NO STATUS ENTRY'
    else:
        ref = rk.get('Q') if ring == 'Q' else min(x for x in rk.values() if x)
        allmin = min(x for x in rk.values() if x)
        tag = f'best ZT {rk.get("ZT")} Z {rk.get("Z")} Q {rk.get("Q")}'
        if bound < allmin: tag += '   <<< BELOW EVERY CATALOG RANK'; cand.append((ring, key, mm, bound, path))
        elif ring == 'Q' and ref and bound < ref: tag += '   << below the Q rank'; cand.append((ring, key, mm, bound, path))
    short = path.split('/schemes/')[-1]
    print(f'{ring:2} {key:9} m={mm:5} -> {bound:5}   {tag}   {short}{"  |" + rest if rest else ""}')
print(f'{len(cand)} candidate records')
for c in cand: print('  CANDIDATE', c)
