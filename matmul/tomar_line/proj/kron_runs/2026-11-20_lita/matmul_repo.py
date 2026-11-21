#!/usr/bin/env python3
"""matmul_repo.py OUT_DIR TABLE.json: the publishable form of the certified schemes of exact/.

For every shape whose best certified rank is below Sedoglavic's table and is not implied by a larger certified
format (sub-format monotonicity), OUT_DIR/large/<shape>_<rank>_<ring>/ gets
  <shape>_m<rank>_Q.json.gz   the scheme (catalog layout, sparse rows), provenance note without local paths;
                              left out when it is above 10 MB (the paths and the certificate stay)
  path_1.json, path_2.json..  the kronkill paths from LITA's square down to the scheme (sources as basenames)
  certificate.log             kronexact's log of the last replay and of the exact Brent check
and OUT_DIR/large_index.md, OUT_DIR/large.json hold the table rows.  Nothing here touches the mat_mul clone."""
import gzip, io, json, math, os, re, sys, time
LIMIT = 10 * 10 ** 6
here = os.path.dirname(os.path.abspath(__file__))
out, table = sys.argv[1], sys.argv[2]
tab = {tuple(e['format']): e['rank'] for e in json.load(open(table))['entries']}
EX = os.path.join(here, 'exact')
best = {}
for f in os.listdir(EX):
    mt = re.fullmatch(r'(\d+)x(\d+)x(\d+)_m(\d+)_Q\.json\.gz', f)
    if mt:
        shape, m = tuple(map(int, mt.groups()[:3])), int(mt.group(4))
        if shape not in best or m < best[shape]: best[shape] = m
keep = []
for shape, m in sorted(best.items()):
    if shape not in tab or m >= tab[shape]: continue
    if any(s != shape and all(a >= b for a, b in zip(s, shape)) and r <= m for s, r in best.items()): continue
    keep.append((shape, m))
LOCAL = re.compile(r'/(?:Users|private|tmp|home)/[^\s"\']*/')


def chain(stem):
    """Paths from the LITA square to the scheme named stem (first deletion first)."""
    pj = json.load(open(os.path.join(EX, stem + '.path.json')))
    src = os.path.basename(pj['source'])
    pj['source'] = src
    if 'external/lita/json' in json.load(open(os.path.join(EX, stem + '.path.json')))['source']:
        return src, [pj]
    root, before = chain(src[:-len('.json')])
    return root, before + [pj]


rows = []
for shape, m in keep:
    name = '%dx%dx%d' % shape
    stem = '%s_m%d_Q' % (name, m)
    log = open(os.path.join(EX, '%s_m%d.log' % (name, m))).read()
    assert 'VERIFIES EXACTLY; corrupted copy REJECTED' in log, stem
    g = re.findall(r'denominator primes (\[[^\]]*\]) -> (\w+)', log)[-1]
    primes, ring = json.loads(g[0]), g[1]
    root, paths = chain(stem)
    k, r0 = re.fullmatch(r'(\d+)x\d+x\d+_m(\d+)_Q\.json', root).groups()
    dels = [p['sequence'] for p in paths]
    folder = '%s_%d_%s' % (name, m, ring)
    d = os.path.join(out, 'large', folder)
    os.makedirs(d, exist_ok=True)
    for i, p in enumerate(paths):
        json.dump(p, open(os.path.join(d, 'path_%d.json' % (i + 1)), 'w'), separators=(',', ':'))
    clean = LOCAL.sub('', log)
    assert '/Users' not in clean
    open(os.path.join(d, 'certificate.log'), 'w').write(clean)
    raw = gzip.open(os.path.join(EX, stem + '.json.gz'), 'rb').read()
    head = raw[:4000].decode()
    note = json.dumps({'source': 'LITA %sx%sx%s_r%s.npz, github.com/khoruzhii/lita commit 472a79f' % (k, k, k, r0),
                       'deletions': dels, 'paths': ['path_%d.json' % (i + 1) for i in range(len(paths))],
                       'reduction': "LITA's 2-reduction after every deletion",
                       'certified': 'kronexact: every Brent equation, exact integers'}, separators=(',', ':'))
    head2, cnt = re.subn(r'"note":\{[^{}]*\}', lambda _: '"note":' + note, head, count=1)
    assert cnt == 1 and '/Users' not in head2
    buf = io.BytesIO()
    with gzip.GzipFile(filename='', mode='wb', fileobj=buf, mtime=0, compresslevel=9) as gz:
        gz.write(head2.encode() + raw[4000:])
    size = buf.tell()
    has_file = size <= LIMIT          # Greg, 2026-11-20: nothing above 10 MB in the repository; report those in the README
    if has_file:
        open(os.path.join(d, stem + '.json.gz'), 'wb').write(buf.getvalue())
    n = json.loads(re.search(r'"n":(\[[0-9,]*\])', head).group(1))
    when = time.strftime('%Y-%m-%d', time.localtime(os.path.getmtime(os.path.join(EX, stem + '.json.gz'))))
    rows.append({'folder': folder, 'shape': list(shape), 'stored_as': n, 'rank': m, 'table': tab[shape], 'gain': tab[shape] - m,
                 'square': int(k), 'square_rank': int(r0), 'deletions': dels, 'primes': primes, 'ring': ring,
                 'omega': 3 * math.log(m) / math.log(shape[0] * shape[1] * shape[2]),
                 'omega_table': 3 * math.log(tab[shape]) / math.log(shape[0] * shape[1] * shape[2]), 'found': when,
                 'bytes': size, 'scheme_file': has_file})
json.dump(rows, open(os.path.join(out, 'large.json'), 'w'), indent=1)
with open(os.path.join(out, 'large_index.md'), 'w') as f:
    f.write('| Scheme | Format | Rank | Table | Gain | From LITA\'s | Deletions | Invertible | Exponent (table) | Found |\n|---|---|---|---|---|---|---|---|---|---|\n')
    for r in rows:
        s = r['shape']
        f.write('| [%s](large/%s) | ⟨%d×%d×%d⟩ | %d | %d | %d | ⟨%d×%d×%d:%d⟩ | %s | %s | %.6f (%.6f) | %s |\n' % (
            r['folder'], r['folder'], *s, r['rank'], r['table'], r['gain'], r['square'], r['square'], r['square'], r['square_rank'],
            ', '.join(r['deletions']), ', '.join(map(str, r['primes'])) or 'none needed', r['omega'], r['omega_table'], r['found']))
print('%d certified shapes, %d published (below the table and not implied by a larger one), %.1f MB of scheme files, %d reported without a file (above 10 MB)' % (
    len(best), len(rows), sum(r['bytes'] for r in rows if r['scheme_file']) / 2 ** 20, sum(not r['scheme_file'] for r in rows)))
