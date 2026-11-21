#!/usr/bin/env python3
"""mkplans.py KRONEXACT: plans for the products <3,3,6:40> (x) orientation of <3,3,6:40> (formats <9,18,18> and
<18,9,18>, rank 1600) from the two rank-40 schemes in base/, each built and certified by `kronexact build`.
Deletes nothing."""
import json, os, subprocess, sys
here = os.path.dirname(os.path.abspath(__file__))
kx = sys.argv[1]
os.makedirs(os.path.join(here, 'plans'), exist_ok=True)
os.makedirs(os.path.join(here, 'built'), exist_ok=True)
for name in ('dps', 'orig'):
    p = os.path.join(here, 'base', '3x3x6_m40_%s.json' % name)
    s = json.load(open(p))
    if 'm' not in s:
        s['m'] = len(s['u'])
        json.dump(s, open(p, 'w'), separators=(',', ':'))
for a in ('dps', 'orig'):
    for b in ('dps', 'orig'):
        for n2 in ([3, 6, 3], [6, 3, 3]):
            n = [3 * n2[0], 3 * n2[1], 6 * n2[2]]
            tag = '%dx%dx%d_m1600_%s_%s' % (*n, a, b)
            plan = {'out': {'op': 'prod', 'parts': [
                {'op': 'file', 'path': os.path.join(here, 'base', '3x3x6_m40_%s.json' % a)},
                {'op': 'orient', 'n': n2, 'of': {'op': 'file', 'path': os.path.join(here, 'base', '3x3x6_m40_%s.json' % b)}}]},
                'max_rank': 1600, 'note': {'source': '<3,3,6:40> %s (x) <%d,%d,%d:40> %s' % (a, *n2, b)}}
            pp = os.path.join(here, 'plans', tag + '.plan.json')
            json.dump(plan, open(pp, 'w'))
            out = os.path.join(here, 'built', tag + '.json')
            r = subprocess.run([kx, 'build', pp, out], capture_output=True, text=True)
            open(os.path.join(here, 'built', tag + '.log'), 'w').write(r.stdout + r.stderr)
            last = [l for l in (r.stdout + r.stderr).splitlines() if 'RESULT' in l or 'panicked' in l]
            print(tag, 'exit', r.returncode, (last[-1] if last else '')[:150])
