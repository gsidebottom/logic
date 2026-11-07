"""List every AlphaTensor F2 factorization, check it against the matmul tensor, write our .bits.
usage: at_all.py factorizations_f2.npz OUTDIR"""
import sys, io, zipfile, pickle, importlib
import numpy as np
ALLOWED = {('numpy.core.multiarray', '_reconstruct'), ('numpy._core.multiarray', '_reconstruct'),
           ('numpy', 'ndarray'), ('numpy', 'dtype'),
           ('numpy.core.multiarray', 'scalar'), ('numpy._core.multiarray', 'scalar')}
class SafeUnpickler(pickle.Unpickler):
    def find_class(self, module, name):
        if (module, name) not in ALLOWED:
            raise pickle.UnpicklingError(f'refused {module}.{name}')
        return getattr(importlib.import_module(module.replace('numpy.core', 'numpy._core')), name)
def load_npy_bytes(b):
    f = io.BytesIO(b)
    version = np.lib.format.read_magic(f)
    rd = np.lib.format.read_array_header_1_0 if version == (1, 0) else np.lib.format.read_array_header_2_0
    shape, fortran, dtype = rd(f)
    if dtype.hasobject:
        return SafeUnpickler(f).load()
    f.seek(0)
    return np.load(f, allow_pickle=False)
npz, out = sys.argv[1], sys.argv[2]
with zipfile.ZipFile(npz) as z:
    names = sorted(n[:-4] for n in z.namelist() if n.endswith('.npy'))
    for key in names:
        arr = load_npy_bytes(z.read(key + '.npy'))
        u, v, w = (np.asarray(arr[0]) & 1), (np.asarray(arr[1]) & 1), (np.asarray(arr[2]) & 1)
        n1, n2, n3 = map(int, key.split(','))
        r = u.shape[1]
        # AlphaTensor convention: a index i*n2+j, b index j*n3+k, c index k*n1+i; T = sum_m u_m (x) v_m (x) w_m
        T = np.einsum('am,bm,cm->abc', u, v, w) % 2
        E = np.zeros_like(T)
        for i in range(n1):
            for j in range(n2):
                for k in range(n3):
                    E[i*n2+j, j*n3+k, k*n1+i] = 1
        ok = np.array_equal(T, E)
        bits = []
        for m in range(r): bits += [int(x) for x in u[:, m]]
        for m in range(r): bits += [int(x) for x in v[:, m]]
        for m in range(r):
            row = [0]*(n1*n3)
            for k in range(n3):
                for i in range(n1):
                    row[i*n3+k] = int(w[k*n1+i, m])
            bits += row
        open(f'{out}/at{n1}{n2}{n3}_{r}.bits', 'w').write(''.join(map(str, bits)) + '\n')
        print(f'{key}: rank {r} tensor-check {"OK" if ok else "FAIL"} -> at{n1}{n2}{n3}_{r}.bits')
