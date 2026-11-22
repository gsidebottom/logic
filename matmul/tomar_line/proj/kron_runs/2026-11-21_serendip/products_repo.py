#!/usr/bin/env python3
"""products_repo.py stage  OUT_DIR FINAL.json MAT_MUL_CLONE
   products_repo.py finish OUT_DIR TABLE.json

The publishable form of the product schemes and of the deletions from them (final_list.py's primary rows of
kind prod and del).  Nothing here touches the mat_mul clone; it is only read, to check that the two schemes of
ours that two plans use are the files it already has.

Every scheme is published with its dimensions SORTED (Greg, 2026-11-21: the stored format is the format of the
tables).  The local schemes are in whatever orientation the product came out in, so stage ends every plan with
the rotations / transpositions that sort it, and rewrites every deletion path for the turned source scheme (the
deleted dimension and the direction of every reduction step are renamed; nothing else changes).

stage writes, for every such row, OUT_DIR/products/<shape>_<rank>/ with
  product    plan.json                       the build plan, every file named without a local path:
                                               {"op":"file","catalog":P}  P inside Perminov's catalog at f70078c
                                               {"op":"file","here":P}     P relative to the plan's directory
  deletion   source_plan.json, path_1.json   the plan of the product scheme it starts from and the kronkill path
and OUT_DIR/products/base/ (the rank-40 <3x3x6> scheme the catalog's JSON files do not have) and
work/jobs.tsv beside OUT_DIR (folder, kind, scheme file name, the certified original it is compared with), so
that OUT_DIR holds only what goes into the repository.

products_build.zsh then runs `kronexact build` / `kronexact replay` INSIDE each folder, so that the scheme file
and certificate.log of a folder are exactly what a reader gets from the files of that folder.

finish checks every folder (certificate, dimensions sorted, size, no local path anywhere; with code of its own it
turns the certified original the same way and reports which schemes are not equal to it), renames the folders to
<shape>_<rank>_<ring> and writes products/index.json and products/INDEX.md.  products_readme.py then makes the
README from them.  Deletes nothing."""
import gzip, json, math, os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
MATMUL = os.path.abspath(os.path.join(here, '..', '..', '..', '..'))                    # logic/matmul
CAT = os.path.join(MATMUL, 'perminov_cache', 'catalog_f70078c') + os.sep
KRED = os.path.join(MATMUL, 'tomar_line', 'proj', 'kron_reduced') + os.sep
R336 = os.path.abspath(os.path.join(here, '..', '2026-11-21_336'))
BASE40 = os.path.join(R336, 'base', '3x3x6_m40_dps.json')
BASE40_NAME = '3x3x6_m40_DPS-accurate.json'
LIMIT = 10 * 10 ** 6
CERT = 'kronexact: every Brent equation, exact integers'
CATALOG = 'github.com/dronperminov/FastMatrixMultiplication at commit f70078c; a file node with "catalog" is a path in it'
mode, out = sys.argv[1], sys.argv[2]
P, W = os.path.join(out, 'products'), os.path.join(os.path.dirname(os.path.abspath(out)), 'work')   # work/ beside OUT_DIR, not in it


def stem_of(path):
    return re.sub(r'(\.plan)?(\.path)?\.json(\.gz)?$', '', os.path.basename(path))


def fmt(n): return '⟨%d×%d×%d⟩' % tuple(n)


def dims_of(path):
    """n of a scheme file written by kronexact (keys sorted: m, n, note, ...), from its first bytes."""
    head = (gzip.open(path, 'rb') if path.endswith('.gz') else open(path, 'rb')).read(200)
    return json.loads(re.search(rb'"n":(\[[0-9,]*\])', head).group(1))


# kronexact's two moves: r = rotate <n0,n1,n2> -> <n1,n2,n0>, (u,v,w) -> (v,w,u);
#                        t = transpose <n0,n1,n2> -> <n0,n2,n1>, (u,v,w) -> (w^T,v^T,u^T).  Products keep their order.
TURNS = ['', 'r', 'rr', 't', 'tr', 'trr']


def perms(turn):
    """(dims, fac) of a sequence of moves: new dimension a is old dimension dims[a], new factor a is old factor fac[a]."""
    dims, fac = [0, 1, 2], [0, 1, 2]
    for o in turn:
        if o == 'r': dims, fac = [dims[1], dims[2], dims[0]], [fac[1], fac[2], fac[0]]
        else: dims, fac = [dims[0], dims[2], dims[1]], [fac[2], fac[1], fac[0]]
    return dims, fac


def turned(n, turn): return [n[a] for a in perms(turn)[0]]


def sorting_turn(n):
    """The first sequence of moves that sorts the dimensions n."""
    return next(t for t in TURNS if turned(n, t) == sorted(n))


def wrap(node, turn):
    for o in turn: node = {'op': 'rotate' if o == 'r' else 'transpose', 'of': node}
    return node


def turn_scheme(d, turn):
    """(n, [u, v, w]) of the scheme d (parsed JSON, sparse rows) after the moves, rows as sorted (index, value) lists.
    Written independently of kronexact, to compare its turned outputs with the certified originals."""
    n = list(d['n'])
    x = [[[(e['index'], e['value']) for e in row] for row in d[k]] for k in 'uvw']

    def tr(rows, r, c):                                  # c x r (index b * r + a) -> r x c (index a * c + b)
        return [sorted(((i % r) * c + i // r, v) for i, v in row) for row in rows]
    for o in turn:
        if o == 'r': n, x = [n[1], n[2], n[0]], [x[1], x[2], x[0]]
        else: n, x = [n[0], n[2], n[1]], [tr(x[2], n[0], n[2]), tr(x[1], n[2], n[1]), tr(x[0], n[1], n[0])]
    return n, x


def same_after_turn(job):
    """Is the published scheme the certified original turned by `turn`?  (folder, True / False)"""
    folder, gz, orig, turn = job
    a = json.load(gzip.open(gz, 'rt'))
    b = json.load(gzip.open(orig, 'rt') if orig.endswith('.gz') else open(orig))
    return folder, turn_scheme(a, '') == turn_scheme(b, turn)


if mode == 'stage':
    rows = [r for r in json.load(open(sys.argv[3])) if r['kind'] in ('prod', 'del') and r['primary']]
    clone = sys.argv[4]
    os.makedirs(os.path.join(P, 'base'), exist_ok=True); os.makedirs(W, exist_ok=True)
    # the rank-40 block: DPS's accurate form of Smirnov's scheme, PLinOpt data/3x3x6_40_DPS-accurate, catalog layout
    b40 = json.load(open(BASE40))
    b40 = {'m': b40['m'], 'n': b40['n'], 'note': {
        'scheme': "Smirnov's <3x3x6:40> in the accurate form of Dumas, Pernet and Sedoglavic",
        'source': 'PLinOpt (github.com/jgdumas/plinopt) data/3x3x6_40_DPS-accurate_{L,R,P}.sms, rewritten in the catalog JSON layout'},
        'u': b40['u'], 'v': b40['v'], 'w': b40['w']}
    json.dump(b40, open(os.path.join(P, 'base', BASE40_NAME), 'w'), separators=(',', ':'))
    own = {}                                             # our own schemes used as files -> their place in mat_mul

    def public(node):
        """A plan node with every file named without a local path."""
        if isinstance(node, list): return [public(x) for x in node]
        if not isinstance(node, dict): return node
        if node.get('op') == 'file':
            p = node['path']
            if p.startswith(CAT): return {'op': 'file', 'catalog': p[len(CAT):]}
            if os.path.abspath(p) == BASE40: return {'op': 'file', 'here': '../base/' + BASE40_NAME}
            if p.startswith(KRED):
                b = os.path.basename(p)
                if b not in own:
                    a, bb, c, m = re.fullmatch(r'(\d+)x(\d+)x(\d+)_m(\d+)_Q\.json\.gz', b).groups()
                    hit = [d for d in os.listdir(os.path.join(clone, 'schemes')) if d.startswith('%sx%sx%s_%s_' % (a, bb, c, m))]
                    assert len(hit) == 1, (b, hit)
                    rel = 'schemes/%s/%s' % (hit[0], b)
                    x, y = (json.load(gzip.open(q, 'rt')) for q in (p, os.path.join(clone, rel)))
                    assert all(x[k] == y[k] for k in ('n', 'm', 'u', 'v', 'w')), 'the copy in mat_mul differs: ' + b
                    own[b] = '../../' + rel
                return {'op': 'file', 'here': own[b]}
            raise SystemExit('a plan names a file that is not public: ' + p)
        return {k: public(v) for k, v in node.items()}

    def public_plan(path, turn, built_as):
        """The plan at `path` with public file names, ending with the moves `turn` (built_as: its format before them)."""
        j = json.load(open(path))
        n = j['note']
        if 'method' in n:
            note = {'construction': 'serendipitous (shared-factor) product as in Perminov, arXiv:2606.02480, Section 2.5',
                    'base': n['s1'], 'second_format': n['s2'], 'replaced': n['replaced'], 'certified': CERT}
        else:                                            # the plain product of the 336 run
            assert n['source'] == '<3,3,6:40> dps (x) <3,6,3:40> dps', n
            note = {'construction': 'Kronecker product <3x3x6:40> (x) <3x6x3:40>', 'base': BASE40_NAME, 'second_format': [3, 6, 3],
                    'replaced': [], 'certified': CERT}
        note.update(built_as=built_as, stored_as=turned(built_as, turn))
        q = {'catalog': CATALOG, 'defs': public(j.get('defs', {})), 'max_rank': j['max_rank'], 'note': note, 'out': wrap(public(j['out']), turn)}
        text = json.dumps(q, separators=(',', ':'))
        assert here[:6] not in text and '/Users' not in text
        return text, note

    def plan_of(product_stem):
        """The plan that built built/<stem>.json.gz: the first line of its build log names it."""
        line = open(os.path.join(here, 'logs', product_stem + '.log')).readline()
        p = os.path.join(here, line.split(':')[0])
        assert p.endswith('.plan.json') and os.path.exists(p), line
        return p

    jobs = []
    for r in rows:
        f = r['format']
        folder = '%dx%dx%d_%d' % (*f, r['rank'])
        d = os.path.join(P, folder)
        os.makedirs(d, exist_ok=True)
        orig = os.path.abspath(os.path.join(here, r['file']))
        stem = stem_of(orig)
        info = {'folder': folder, 'shape': f, 'rank': r['rank'], 'table': r['table'], 'gain': r['table'] - r['rank'],
                'own': min(r['bar'], r['others'] if r['others'] is not None else r['bar']) - r['rank']}
        n_nat = dims_of(orig)                              # the certified scheme as it stands locally
        if r['kind'] == 'prod':
            turn = sorting_turn(n_nat)
            src_nat = n_nat
            text, note = public_plan(plan_of(stem), turn, n_nat)
            open(os.path.join(d, 'plan.json'), 'w').write(text)
            info.update(kind='product')
        else:
            in336 = orig.startswith(R336)
            pj = json.load(open(os.path.join(R336, 'paths', stem + '.path.json') if in336 else os.path.join(here, 'reduce', 'dpaths', stem + '.path.json')))
            src = stem_of(pj['source'])
            assert pj['n'] == n_nat, (stem, pj['n'], n_nat)
            turn = sorting_turn(n_nat)                     # the deleted scheme must come out sorted
            dims, fac = perms(turn)
            letter = lambda x: 'IJK'[dims.index('IJK'.index(x[0]))] + x[1:]      # the same index of the same dimension, renamed
            src_nat = list(n_nat)
            for x in pj['sequence'].split(','): src_nat['IJK'.index(x[0])] += 1
            sm = int(re.match(r'\d+x\d+x\d+_m(\d+)', src).group(1))
            text, note = public_plan(os.path.join(R336, 'plans', src + '.plan.json') if in336 else plan_of(src), turn, src_nat)
            open(os.path.join(d, 'source_plan.json'), 'w').write(text)
            # the path for the turned source: dimensions and reduction directions renamed, everything else as found
            pj['source'] = 'source_plan.json'
            pj['n'] = turned(pj['n'], turn)
            pj['sequence'] = ','.join(letter(x) for x in pj['sequence'].split(','))
            for st in pj['stages']:
                if st['delete']: st['delete'] = letter(st['delete'])
                st['n'] = turned(st['n'], turn)
                for x in st['steps']:
                    x['direction'] = fac.index(x['direction'])
                    if 'seen' in x: x['seen'] = {str(fac.index(int(k))): v for k, v in x['seen'].items()}
            ptext = json.dumps(pj, separators=(',', ':'))
            assert '/Users' not in ptext
            open(os.path.join(d, 'path_1.json'), 'w').write(ptext)
            info.update(kind='deletion', deletions=pj['sequence'], source=turned(src_nat, turn), source_rank=sm)
            assert [a - sum(x[0] == 'IJK'[i] for x in pj['sequence'].split(',')) for i, a in enumerate(info['source'])] == f
        b = re.match(r'(\d+)x(\d+)x(\d+)_m(\d+)', note['base'])
        base_nat = list(map(int, b.groups()[:3]))
        assert [x * y for x, y in zip(base_nat, note['second_format'])] == src_nat, (folder, base_nat, note['second_format'], src_nat)
        # base scheme and block sizes in the published orientation: position by position they multiply to the format
        info.update(base_shape=turned(base_nat, turn), base_rank=int(b.group(4)), base=note['base'],
                    block_sizes=turned(note['second_format'], turn), turn=turn,
                    built={'base': base_nat, 'block_sizes': note['second_format'], 'replaced': note['replaced'], 'format': src_nat})
        jobs.append((folder, info['kind'], '%dx%dx%d_m%d.json' % (*f, r['rank']), orig, json.dumps(info)))
    with open(os.path.join(W, 'jobs.tsv'), 'w') as fh:
        for j in jobs: fh.write('\t'.join(j) + '\n')
    print('%d folders staged (%d products, %d deletions); our own schemes used as files: %s' % (
        len(jobs), sum(j[1] == 'product' for j in jobs), sum(j[1] == 'deletion' for j in jobs), sorted(own.values())))

elif mode == 'finish':
    tab = {tuple(e['format']): e['rank'] for e in json.load(open(sys.argv[3]))['entries']}
    rows, bad, compare = [], [], []
    for line in open(os.path.join(W, 'jobs.tsv')):
        folder, kind, name, orig, info = line.rstrip('\n').split('\t')
        info = json.loads(info)
        d = os.path.join(P, folder)
        if not os.path.isdir(d):                         # already renamed by an earlier finish
            d = [os.path.join(P, x) for x in os.listdir(P) if x.startswith(folder + '_')][0]
        log = open(os.path.join(d, 'certificate.log')).read()
        gz = os.path.join(d, name + '.gz')
        if 'VERIFIES EXACTLY; corrupted copy REJECTED' not in log or not os.path.exists(gz): bad.append(folder + ': not certified'); continue
        n = dims_of(gz)
        if n != info['shape']: bad.append('%s: stored as %s, not sorted' % (folder, n)); continue
        compare.append((folder, gz, orig, info['turn']))
        size = os.path.getsize(gz)
        if size > LIMIT: bad.append(folder + ': above 10 MB')
        for fn in os.listdir(d):
            if not fn.endswith('.gz'):
                t = open(os.path.join(d, fn)).read()
                if '/Users' in t or '/private' in t or '/tmp' in t: bad.append('%s/%s: local path' % (folder, fn))
        head = gzip.open(gz, 'rb').read(3000)
        if b'/Users' in head or b'/private' in head: bad.append(folder + ': local path in the scheme note')
        g = re.findall(r'denominator primes (\[[^\]]*\]) -> (\w+)', log)[-1]
        s = info['shape']; vol = s[0] * s[1] * s[2]
        assert tab[tuple(s)] == info['table']
        info.update(primes=json.loads(g[0]), ring=g[1], bytes=size, scheme=name + '.gz',
                    omega=3 * math.log(info['rank']) / math.log(vol), omega_table=3 * math.log(info['table']) / math.log(vol))
        info['folder'] = '%s_%s' % (folder, g[1])
        rows.append((d, info))
    # The published scheme against the certified original, turned here by other code.  A difference is reported, not
    # fatal: the folder's own certificate is the exact check of the file that is published.  (One known case:
    # 14x28x28_6279, first built at 01:25 on 2026-11-21 by an earlier builder that wrote 504 replaced products in
    # another, equivalent form.)
    if not bad:
        import multiprocessing
        with multiprocessing.get_context('fork').Pool(12) as pool:      # fork: the workers must not re-run this script
            differs = sorted(fo for fo, same in pool.imap_unordered(same_after_turn, compare, chunksize=4) if not same)
        for d, info in rows:
            if os.path.basename(d) != info['folder']: os.rename(d, os.path.join(P, info['folder']))
    rows = [info for _, info in rows]
    if bad:
        print('\n'.join(bad)); raise SystemExit('%d problems; index not written' % len(bad))
    rows.sort(key=lambda r: (r['shape'], r['rank']))
    json.dump(rows, open(os.path.join(P, 'index.json'), 'w'), indent=1)

    def how(r):
        s = 'base ⟨%d×%d×%d:%d⟩, blocks %s' % (*r['base_shape'], r['base_rank'], fmt(r['block_sizes']))
        if r['kind'] == 'deletion':
            return '⟨%d×%d×%d:%d⟩ (%s), %s' % (*r['source'], r['source_rank'], s, ', '.join('`%s`' % x for x in r['deletions'].split(',')))
        return s

    def inv(r): return ', '.join(map(str, r['primes'])) or 'none'
    with open(os.path.join(P, 'INDEX.md'), 'w') as f:
        f.write('# products/: the full table\n\n'
                'Every scheme of this folder, against Sedoglavic\'s table of 2026-11-15.  "Own" is the gain beyond what that table\n'
                'and the other schemes of this repository imply by sub-format, split and Kronecker product.  Every scheme is\n'
                'stored with its dimensions in the order of "Format".  For a product, "Construction" is the base scheme and the\n'
                'block sizes ⟨p×q×s⟩ (every entry of A becomes a p×q block, of B a q×s block, of C a p×s block), written so that\n'
                'position by position they multiply to the format; the catalog file may hold the base scheme with its dimensions\n'
                'in another order.  For a deletion it is the product scheme it starts from, made the same way, and the deleted\n'
                'indices: in ⟨m×k×n⟩, `I5` removes row 5 of A (and of C), `J5` the inner index 5 and `K5` column 5 of B, counted\n'
                'from 0.  "Invertible" lists the primes that occur in denominators.  See the README for the method and the\n'
                'credits.\n\n'
                '| Scheme | Format | Rank | Table | Gain | Own | Kind | Construction | Invertible | Exponent (table\'s) |\n|---|---|---|---|---|---|---|---|---|---|\n')
        for r in rows:
            f.write('| [%s](%s) | %s | %d | %d | %d | %d | %s | %s | %s | %.4f (%.4f) |\n' % (
                r['folder'], r['folder'], fmt(r['shape']), r['rank'], r['table'], r['gain'], r['own'], r['kind'], how(r), inv(r), r['omega'], r['omega_table']))
    pr = [r for r in rows if r['kind'] == 'product']; de = [r for r in rows if r['kind'] == 'deletion']
    print('%d schemes equal the certified originals turned to sorted dimensions; in another form, certified on their own: %s' % (len(rows) - len(differs), differs or 'none'))
    print('%d folders: %d products, %d deletions; %.1f MB of scheme files, largest %.2f MB; products/index.json and products/INDEX.md written' % (
        len(rows), len(pr), len(de), sum(r['bytes'] for r in rows) / 1e6, max(r['bytes'] for r in rows) / 1e6))
else:
    raise SystemExit(__doc__)
