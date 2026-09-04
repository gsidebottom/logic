#!/usr/bin/env python3
"""Export the 331 sampled frontier states with their final exact-rank verdicts
(frontier_analysis.py at 60 s cadical, then frontier_ab.py's four arms) as
one line each:  VERDICT k da db dc  <da*db hex masks t[a][b] over c>
VERDICT: leaflim (rank >= k), genuine (rank <= k-1), open.  (2026-09-04)"""
import re, csv, random, sys, os
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier_analysis import parse, PER_CLASS
recs = parse('matmul/r22/frontier19.txt')
finals = [r for r in recs if r['kind'] == 'final' and r['tensor'] is not None]
seen = {}
for r in finals:
    seen.setdefault((tuple(tuple(row) for row in r['tensor']), r['k']), r)
by = defaultdict(list)
for r in seen.values():
    by[(tuple(sorted(r['dims'])), r['k'])].append(r)
random.seed(11)
ordered = []
for (dims, k), rs in sorted(by.items(), key=lambda kv: (kv[0][0][0] * kv[0][0][1] * kv[0][0][2], kv[0][1])):
    for r in random.sample(rs, min(PER_CLASS, len(rs))):
        ordered.append(r)
pat = re.compile(r"\s+dims \((\d+), (\d+), (\d+)\) k (\d+) lb (\d+) compressed \S+: rank<=(\d+) (\w+)")
verdicts = [m.group(7) for m in (pat.match(l) for l in open('matmul/r22/frontier19_report.txt')) if m]
ab = defaultdict(dict)
for row in csv.DictReader(open('matmul/r22/frontier_ab/results.csv')):
    ab[int(row['idx'])][row['arm']] = row['result']
for idx, d in ab.items():
    assert verdicts[idx] == 'TIMEOUT'
    verdicts[idx] = 'UNSAT' if 'UNSAT' in d.values() else 'SAT' if 'SAT' in d.values() else 'TIMEOUT'
name = {'UNSAT': 'leaflim', 'SAT': 'genuine', 'TIMEOUT': 'open'}
out = open('matmul/r22/frontier_probe_set.txt', 'w')
from collections import Counter
c = Counter()
for r, v in zip(ordered, verdicts):
    da, db, dc = r['dims']
    hexes = " ".join(f"{r['tensor'][a][b]:03x}" for a in range(da) for b in range(db))
    out.write(f"{name[v]} {r['k']} {da} {db} {dc} {hexes}\n")
    c[name[v]] += 1
print(dict(c))
