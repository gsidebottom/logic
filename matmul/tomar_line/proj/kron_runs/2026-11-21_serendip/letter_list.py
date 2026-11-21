#!/usr/bin/env python3
"""letter_list.py FINAL.json OUT.csv: the product and deletion-from-product rows of final_list.py's output as a
small table to send with a note: one row per format with its rank, the table's rank, what kind of result it is,
the coefficient ring and how the scheme was made.  Reads only; writes OUT.csv.

Columns of OUT.csv:
  format                 sorted format, e.g. 9x9x27
  rank                   rank of our certified scheme
  table_2026-11-15       rank in Sedoglavic's table (fmm_digest 8e6ad05)
  gain                   table - rank
  kind                   product  = shared-factor (serendipitous) product built by `kronexact build`
                         deletion = one deletion from a product scheme followed by LITA's 2-reduction
  implied_by_other_rows  yes when sub-format, split or Kronecker product applied to the table and our other
                         schemes already gives this rank or less (final_list.py's "primary" flag, negated)
  best_from_other_rows   the best rank those operations give, i.e. what the row has to beat
  coefficients           integer / Z[1/2] / rational with the primes in denominators (products: read from the
                         build log; deletions: not tabulated)
  construction           products: base scheme, second factor and the blocks that were replaced, from the plan;
                         deletions: the deleted index and the product scheme it was deleted from, from the path

It needs the run directory as it is on disk: logs/ and the plans*/ directories (tracked as logs.tgz and
plans.tgz) and reduce/dpaths/ (reduce/dpaths.tgz)."""
import csv, json, os, re, sys
here = os.path.dirname(os.path.abspath(__file__))
rows = json.load(open(sys.argv[1]))
out = []
for y in rows:
    if y['kind'] not in ('prod', 'del'): continue        # LITA deletions and catalog projections are published already
    b = os.path.basename(y['file']); b = b[:-len('.json.gz')] if b.endswith('.gz') else b[:-len('.json')]
    ring, how = '', ''
    if y['kind'] == 'prod':
        # ring: kronexact's build log lists the primes that occur in denominators
        t = open(os.path.join(here, 'logs', b + '.log')).read()
        g = re.search(r'denominator primes (\[[^\]]*\]) -> (\w+)', t)
        if g: ring = 'integer' if g.group(1) == '[]' else ('Z[1/2]' if g.group(2) == 'dyadic' else 'rational, primes ' + g.group(1)[1:-1])
        # construction: the plan that built it; later plan directories override the first screen's
        for d in ('plans_sub', 'plans_grid', 'plans_40', 'plans_rest', 'plans'):
            p = os.path.join(here, d, b + '.plan.json')
            if os.path.exists(p):
                n = json.load(open(p))['note']
                s1 = re.sub(r'_[0-9a-f]{40}', '', str(n.get('s1', ''))).replace('.json', '')    # catalog name without its hash
                blocks = sorted({json.dumps(x) for x in n.get('replaced', [])})
                how = 'product of %s with <%s>; blocks replaced: %s' % (s1, ','.join(map(str, n.get('s2', []))), ' '.join(blocks)[:160])
                break
    else:
        # deletion: the file name carries the deleted indices, the kronkill path names the source scheme
        g = re.fullmatch(r'\d+x\d+x\d+_m\d+_(\w+)', b)
        pth = os.path.join(here, 'reduce', 'dpaths', b + '.path.json')
        src = ''
        if os.path.exists(pth): src = os.path.basename(json.load(open(pth))['source']).replace('.json', '')
        elif '2026-11-21_336' in y['file']: src = '<3,3,6:40> (x) <3,6,3:40> = 9x18x18_m1600'
        how = 'deletion %s from the product scheme %s, then 2-reduction' % (g.group(1).replace('_', ', '), src)
        ring = 'rational, primes not tabulated'
    # what the table and our other schemes imply for this format without this file
    best_other = min(y['bar'], y['others']) if y['others'] is not None else y['bar']
    out.append(['x'.join(map(str, y['format'])), y['rank'], y['table'], y['table'] - y['rank'],
                'product' if y['kind'] == 'prod' else 'deletion', 'no' if y['primary'] else 'yes', best_other, ring, how])
out.sort(key=lambda r: tuple(map(int, r[0].split('x'))))
w = csv.writer(open(sys.argv[2], 'w'))
w.writerow(['format', 'rank', 'table_2026-11-15', 'gain', 'kind', 'implied_by_other_rows', 'best_from_other_rows', 'coefficients', 'construction'])
w.writerows(out)
print(len(out), 'rows')
