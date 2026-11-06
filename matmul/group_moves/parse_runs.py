#!/usr/bin/env python3
"""Summarize flip A/B logs: first time each rank was reached, final counters."""
import re, sys, glob, os
def parse(path):
    first = {}; last_report = None; done = None
    for line in open(path, errors='replace'):
        m = re.match(r'c \[\s*([\d.]+)s\] worker min rank (\d+)', line)
        if m:
            t, r = float(m.group(1)), int(m.group(2)); first.setdefault(r, t)
        m = re.match(r'c \[\s*([\d.]+)s\] new min rank (\d+)', line)
        if m:
            t, r = float(m.group(1)), int(m.group(2)); first.setdefault(r, t)
        if line.startswith('c [') and 'reductions' in line:
            last_report = line.strip()
        if line.startswith('c DONE'):
            done = line.strip()
    return first, last_report, done
logs = sorted(glob.glob(os.path.join(sys.argv[1], '*.log')))
for lg in logs:
    first, rep, done = parse(lg)
    name = os.path.basename(lg)[:-4]
    ranks = sorted(first)
    prof = ' '.join(f'{r}@{first[r]:.0f}s' for r in ranks[:12])
    print(f'== {name}')
    print(f'   min rank {ranks[0] if ranks else "?"} | first arrivals: {prof}')
    if rep:
        m = re.search(r'reductions (\d+) \| landings (\d+) \| distinct (\[.*?\]) \| trajectories (\d+) \| diffuse-flips ([\d.]+)M(.*)', rep)
        if m:
            print(f'   reductions {m.group(1)} | landings {m.group(2)} | distinct {m.group(3)} | trajectories {m.group(4)} | flips {m.group(5)}M |{m.group(6)}')
    if done:
        print('   ' + done)
