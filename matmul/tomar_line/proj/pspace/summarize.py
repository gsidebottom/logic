"""Summarize a decay run: per flip distance, how many mutants' projections reach 47 / 48 / 49 in the short descent.
usage: summarize.py decay_X.stdout"""
import sys, re, collections
pat = re.compile(r'^(base_s\d+|k(\d+)_m\d+) seeds (\d+) \| c DONE: min rank (\d+); distinct landings by rank: \[(.*?)\] \| 47 files (\d+)')
rows = collections.defaultdict(list)
for line in open(sys.argv[1]):
    m = pat.match(line.strip())
    if not m: continue
    tag, k, seeds, minr, dist, n47 = m.groups()
    d = dict((int(a), int(b)) for a, b in re.findall(r'\((\d+), (\d+)\)', dist))
    rows['base' if k is None else int(k)].append((int(minr), d.get(47, 0), d.get(48, 0), int(seeds)))
print(f"{'distance':>8} {'n':>3} {'min47':>5} {'min48':>5} {'min49+':>6} {'mean#47':>7} {'mean#48':>7}")
for k in sorted(rows, key=lambda x: (-1 if x == 'base' else x)):
    v = rows[k]; n = len(v)
    r47 = sum(1 for x in v if x[0] == 47); r48 = sum(1 for x in v if x[0] == 48); r49 = n - r47 - r48
    print(f"{str(k):>8} {n:>3} {r47:>5} {r48:>5} {r49:>6} {sum(x[1] for x in v)/n:>7.2f} {sum(x[2] for x in v)/n:>7.1f}")
