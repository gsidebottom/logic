#!/usr/bin/env python3
"""update_readme.py MAT_MUL_DIR STAGE_DIR [--interim]: rewrite the block between <!-- large:begin --> and
<!-- large:end --> of mat_mul's README.md from STAGE_DIR/large.json (written by matmul_repo.py)."""
import json, os, sys, time
mm, stage = sys.argv[1], sys.argv[2]
rows = json.load(open(os.path.join(stage, 'large.json')))
interim = '--interim' in sys.argv
ks = sorted({r['square'] for r in rows})
gain = sum(r['gain'] for r in rows)
txt = []
small = [r for r in rows if max(r['shape']) <= 16]
head = '%d formats with a dimension above 16' % (len(rows) - len(small))
if small:
    head += ' and %s' % ', '.join('⟨%d×%d×%d⟩' % tuple(r['shape']) for r in small)
txt.append('%s, each below Sedoglavic\'s table of 2026-11-15 (by %d to %d products, %s in '
           'total).  Every scheme is one of LITA\'s square schemes ⟨k×k×k⟩ (here k = %s) with one or more indices deleted, '
           'each deletion followed by LITA\'s 2-reduction.  The square schemes and the reduction are theirs; the choice of '
           'deletions and of the products to drop is ours.' % (
               head, min(r['gain'] for r in rows), max(r['gain'] for r in rows), format(gain, ','),
               ', '.join(map(str, ks))))
txt.append('')
txt.append('- **Deletions.** `I5` removes row 5 of A, `J5` the inner index 5 (a column of A with the matching row of B) and '
           '`K5` column 5 of B, counted from 0 in the scheme as it stands after the earlier deletions.')
txt.append('- **Coefficients.** All are rational; "Invertible" lists the primes that occur in denominators.')
txt.append('- **What is listed.** The lowest rank we certified for each format, and only formats for which no larger format '
           'in this list has the same or a lower rank.')
txt.append('- **Form.** Compressed JSON in [large/](large), one folder per scheme, not PLinOpt files: see [Files](#files).  '
           'Each was certified by evaluating every Brent equation in exact integer arithmetic '
           '([checks/check_large.log](checks/check_large.log)).')
nofile = [r for r in rows if not r.get('scheme_file', True)]
if nofile:
    txt.append('- **No file above 10 MB.** %d schemes marked "no file" are reported here only: their compressed files are '
               '%.0f to %.0f MB.  Each of their folders holds the paths and the certificate log, which ends with the exact check '
               'of the scheme; `tools/kronexact replay` on the paths rebuilds and re-certifies it from LITA\'s file.' % (
                   len(nofile), min(r['bytes'] for r in nofile) / 1e6, max(r['bytes'] for r in nofile) / 1e6))
if interim:
    txt.append('- **Status.** Written %s while the searches on the larger squares were still running; more formats will follow.'
               % time.strftime('%Y-%m-%d %H:%M'))
txt.append('')
txt.append('| Scheme | Format | Rank | Table | Gain | From LITA\'s | Deletions | Invertible | Exponent (table\'s) | Found |')
txt.append('|---|---|---|---|---|---|---|---|---|---|')
for r in rows:
    s = r['shape']
    txt.append('| [%s](large/%s)%s | ⟨%d×%d×%d⟩ | %d | %d | %d | ⟨%d×%d×%d:%d⟩ | %s | %s | %.6f (%.6f) | %s |' % (
        r['folder'], r['folder'], '' if r.get('scheme_file', True) else ' (no file)', *s, r['rank'], r['table'], r['gain'], r['square'], r['square'], r['square'], r['square_rank'],
        ', '.join('`%s`' % d for d in r['deletions']), ', '.join(map(str, r['primes'])), r['omega'], r['omega_table'], r['found']))
p = os.path.join(mm, 'README.md')
s = open(p).read()
a, b = '<!-- large:begin -->', '<!-- large:end -->'
assert s.count(a) == 1 and s.count(b) == 1
i, j = s.index(a) + len(a), s.index(b)
open(p, 'w').write(s[:i] + '\n' + '\n'.join(txt) + '\n' + s[j:])
print('README block: %d rows, total gain %d' % (len(rows), gain))
