"""Convert AlphaTensor F2 factorizations to our .bits layout with a restricted unpickler.
usage: at_to_bits.py factorizations_f2.npz KEY out.bits   (KEY like 3,3,4)
Object arrays are loaded through an Unpickler whose find_class admits only
numpy's array-reconstruction names; anything else raises."""
import sys, io, zipfile, pickle
import numpy as np
ALLOWED = {('numpy.core.multiarray', '_reconstruct'), ('numpy._core.multiarray', '_reconstruct'),
           ('numpy', 'ndarray'), ('numpy', 'dtype'),
           ('numpy.core.multiarray', 'scalar'), ('numpy._core.multiarray', 'scalar')}
class SafeUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        if (module, name) not in ALLOWED:
            raise pickle.UnpicklingError(f'refused {module}.{name}')
        mod = module.replace('numpy.core', 'numpy._core')
        import importlib
        return getattr(importlib.import_module(mod), name)
def load_npy_bytes(b):
    f = io.BytesIO(b)
    version = np.lib.format.read_magic(f)
    rd = np.lib.format.read_array_header_1_0 if version == (1, 0) else np.lib.format.read_array_header_2_0
    shape, fortran, dtype = rd(f)
    if dtype.hasobject:
        return SafeUnpickler(f).load()
    f.seek(0)
    return np.load(f, allow_pickle=False)
npz, key, out = sys.argv[1], sys.argv[2], sys.argv[3]
with zipfile.ZipFile(npz) as z:
    arr = load_npy_bytes(z.read(key + '.npy'))
u, v, w = arr[0], arr[1], arr[2]
n1, n2, n3 = map(int, key.split(','))
assert u.shape[0] == n1*n2 and v.shape[0] == n2*n3 and w.shape[0] == n3*n1, (u.shape, v.shape, w.shape)
r = u.shape[1]
sa, sb, sg = n1*n2, n2*n3, n1*n3
bits = []
# a: index i*n2+j (same as ours); b: j*n3+k (same); w: AlphaTensor index k*n1+i -> our bit i*n3+k
for m in range(r):
    bits += [int(u[t, m]) & 1 for t in range(sa)]
for m in range(r):
    bits += [int(v[t, m]) & 1 for t in range(sb)]
for m in range(r):
    row = [0]*sg
    for k in range(n3):
        for i in range(n1):
            row[i*n3 + k] = int(w[k*n1 + i, m]) & 1
    bits += row
open(out, 'w').write(''.join(map(str, bits)) + '\n')
print(key, 'rank', r, 'bits', len(bits))
