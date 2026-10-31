#!/usr/bin/env python3
"""Is a point one of the finite 'line' points?  In its own coordinates, per mode, count the indices i where
e_i is a [1,1,1] line as a column of the inverse (a col-line) or as a row (a row-line).  A point whose four
indices are all covered in all three modes is fixed by its selections up to diagonal scalings.

  unit_lines.py PREFIX ...
"""
import sys
src = open('/Users/greg/projects/logic/matmul/dps48/rfc2610/canon_enum.py').read()
head = src[:src.index('def rank(vs)')]
for pre in sys.argv[1:]:
    sys.argv = ['x', pre, '/dev/null']
    import io, contextlib
    with contextlib.redirect_stdout(io.StringIO()): exec(head)
    unit = lambda l: sum(1 for x in l if x) == 1
    idx = lambda l: next(i for i, x in enumerate(l) if x)
    out = []
    for m in "XYZ":
        c = {idx(l) for l in col[m] if unit(l)}; r = {idx(l) for l in row[m] if unit(l)}
        out.append(f"{m}: cols {len(c)} rows {len(r)} covered {len(c | r)}")
    cl = sum(1 for p in prods if unit(p['u']) and unit(p['v'])); cr = sum(1 for p in prods if unit(p['r']) and unit(p['s'])); cp = sum(1 for p in prods if unit(p['p']) and unit(p['q']))
    print(f"{pre.split('/')[-1][:30]:30s} canon ({cl},{cr},{cp}) lines {[len(col[m]) for m in 'XYZ']}/{[len(row[m]) for m in 'XYZ']}  " + "; ".join(out))
