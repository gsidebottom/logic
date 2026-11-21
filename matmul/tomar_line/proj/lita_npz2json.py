#!/usr/bin/env python3
"""LITA's scheme files (github.com/khoruzhii/lita, schemes/*.npz, format fmmp.qcsr.v1) -> the catalog JSON layout
that kronkill and the kron_* tools read, with sparse rows [{"index": i, "value": v}, ...].

LITA: U reads A (n1 x n2) row-major, V reads B (n2 x n3) row-major, W writes C = A B (n1 x n3) row-major.
Catalog: u on A, v on B, w on C^T (n3 x n1) row-major, so only W's column index is transposed.

Pure Python (no NumPy, no pickle): the npz is a zip of .npy arrays whose headers are read here.  Data only.
Usage: python3 -I lita_npz2json.py IN.npz OUT.json
"""
import ast, json, struct, sys, zipfile
from fractions import Fraction


def npy(b):
    assert b[:6] == b'\x93NUMPY', 'not an npy array'
    major = b[6]
    hl, off = (struct.unpack('<H', b[8:10])[0], 10) if major == 1 else (struct.unpack('<I', b[8:12])[0], 12)
    h = ast.literal_eval(b[off:off + hl].decode('latin1'))
    assert not h['fortran_order']
    body, d, shape = b[off + hl:], h['descr'], h['shape']
    cnt = 1
    for s in shape:
        cnt *= s
    if d in ('<i8', '<i4'):
        w = int(d[2])
        assert len(body) == cnt * w, 'array length'
        return list(struct.unpack('<%d%s' % (cnt, 'q' if w == 8 else 'i'), body))
    if d.startswith('<U'):
        return body.decode('utf-32-le').rstrip('\x00')
    raise ValueError('unsupported dtype ' + d)


def main(src, dst):
    z = zipfile.ZipFile(src)
    meta = json.loads(npy(z.read('metadata_json.npy')))
    n1, n2, n3 = meta.get('tensor', meta.get('n'))
    m = meta['rank']
    out = {'n': [n1, n2, n3], 'm': m, 'z2': False, 'source': 'github.com/khoruzhii/lita ' + src.split('/')[-1],
           'construction': meta.get('construction', '')}
    nnz, dens = [], set()
    for ax, cols in (('u', n1 * n2), ('v', n2 * n3), ('w', n1 * n3)):
        ptr, idx = npy(z.read(ax + '_indptr.npy')), npy(z.read(ax + '_indices.npy'))
        num, den = npy(z.read(ax + '_numerators.npy')), npy(z.read(ax + '_denominators.npy'))
        assert len(ptr) == m + 1 and ptr[0] == 0 and ptr[-1] == len(idx) == len(num) == len(den), ax + ' CSR lengths'
        rows, cnt = [], 0
        for t in range(m):
            row = {}
            for e in range(ptr[t], ptr[t + 1]):
                j = idx[e]
                assert 0 <= j < cols and den[e] != 0
                if ax == 'w':
                    i, k = divmod(j, n3)
                    j = k * n1 + i
                row[j] = row.get(j, 0) + Fraction(num[e], den[e])
            ent = []
            for j in sorted(row):
                x = row[j]
                if x == 0:
                    continue
                dens.add(x.denominator)
                ent.append({'index': j, 'value': x.numerator if x.denominator == 1 else '%d/%d' % (x.numerator, x.denominator)})
            assert ent, 'a product with a zero factor'
            cnt += len(ent)
            rows.append(ent)
        out[ax] = rows
        nnz.append(cnt)
    with open(dst, 'w') as f:
        json.dump(out, f, separators=(',', ':'))
    print('%s: %dx%dx%d rank %d, nonzeros u/v/w %s, denominators %s' % (src.split('/')[-1], n1, n2, n3, m, nnz, sorted(dens)))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
