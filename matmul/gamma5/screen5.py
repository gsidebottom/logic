#!/usr/bin/env python3
"""Growth factors of square <n x n x n : r> schemes given as .exp files (one product per line,
(sum a_ij)*(sum b_kl)*(sum c_mn)), as AlphaEvolve's python factor matrices, or as PLinOpt
L/R/P .sms files, in all three cyclic roles.  Quantities as in ../gamma3/screen3.py.

  python3 -I screen5.py exp FILE | ae FILE FUNC | sms PREFIX  [--n 5] [--name NAME]
"""
import ast, math, re, sys
if sys.flags.isolated:  # -I drops the user site; numpy lives there
    sys.path.append('/Users/greg/Library/Python/3.9/lib/python/site-packages')
import numpy as np

def parse_exp(path, n):
    """returns alpha, beta, gamma: (r, n*n) arrays of the a-, b-, c-coefficients (row-major index)"""
    rows = []
    term = re.compile(r"([+-]?)(\d*)\*?([abc])(\d)(\d)")
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(")*(")
        assert len(parts) == 3, line
        vecs = []
        for part, letter in zip(parts, "abc"):
            v = np.zeros(n * n)
            s = part.strip("()")
            pos = 0
            for m in term.finditer(s):
                assert m.group(3) == letter, (line, letter)
                c = (-1.0 if m.group(1) == "-" else 1.0) * (float(m.group(2)) if m.group(2) else 1.0)
                v[(int(m.group(4)) - 1) * n + int(m.group(5)) - 1] += c
                pos = m.end()
            assert re.fullmatch(r"[\s]*", s[pos:]), (line, s[pos:])
            vecs.append(v)
        rows.append(vecs)
    return tuple(np.array([r[k] for r in rows]) for k in range(3))

def parse_ae(path, func):
    """AlphaEvolve colab file: the three np.array literals of def FUNC, columns = rank"""
    tree = ast.parse(open(path).read())
    fn = next(nd for nd in ast.walk(tree) if isinstance(nd, ast.FunctionDef) and nd.name == func)
    arrays = [ast.literal_eval(nd.args[0]) for nd in ast.walk(fn) if isinstance(nd, ast.Call) and getattr(nd.func, "attr", "") == "array"]
    assert len(arrays) == 3
    U, V, W = (np.array(a, float) for a in arrays)
    return U.T, V.T, W.T   # (r, n*n)

def parse_sms(path):
    with open(path) as f:
        head = f.readline()
        while head.startswith("#"):
            head = f.readline()
        r, c, _ = head.split()
        M = np.zeros((int(r), int(c)))
        for line in f:
            t = line.split()
            if len(t) < 3 or t[0] == "0":
                break
            i, j = int(t[0]) - 1, int(t[1]) - 1
            M[i, j] = float(eval(t[2], {"__builtins__": {}}, {})) if "/" in t[2] else float(t[2])
    return M

def check(L, R, P, n, rng, trials=4):
    for _ in range(trials):
        A = rng.integers(-3, 4, (n, n)).astype(float); B = rng.integers(-3, 4, (n, n)).astype(float)
        got = P @ ((L @ A.reshape(-1)) * (R @ B.reshape(-1)))
        if not np.allclose(got, (A @ B).reshape(-1)):
            return False
    return True

def to_LRP(x, y, z, n, rng):
    """x, y, z: the three factor sets of each product (r, n*n).  Returns L, R, P = (z[:, T]).T in
    our convention vec(C) = P((L vecA) o (R vecB)), or None if no transposition convention works."""
    T = np.array([n * j + i for i in range(n) for j in range(n)])
    for P in (z[:, T].T, z.T):
        if check(x, y, P, n, rng):
            return x, y, P
    return None

def factors(L, R, P, n):
    l1, r1 = np.abs(L).sum(1), np.abs(R).sum(1)
    l2, r2 = np.linalg.norm(L, axis=1), np.linalg.norm(R, axis=1)
    absP = np.abs(P)
    s_inf = absP @ (l1 * r1); s_2 = absP @ (l2 * r2)
    amp = 0.5 * np.sqrt((P ** 2) @ (l2 ** 2 * r2 ** 2))
    nz = P != 0
    nnzL, nnzR = (L != 0).sum(1), (R != 0).sum(1)
    q0 = max(int(nz[j].sum()) + int(max(nnzL[i] + nnzR[i] for i in np.nonzero(nz[j])[0])) for j in range(n * n))
    adds = int((nnzL - 1).sum() + (nnzR - 1).sum() + (nz.sum(1) - 1).sum())
    return dict(g_infinf=float(s_inf.max()), g_inf2=float(s_2.max()), g_22=float(np.linalg.norm(s_2)),
                g_2=float(np.sum(l2 * r2 * np.linalg.norm(P, axis=0))), Q0=q0, amp=float(amp.max()),
                nnz=int((L != 0).sum() + (R != 0).sum() + nz.sum()), adds=adds,
                maxrow=f"L {int(nnzL.max())} R {int(nnzR.max())} P {int(nz.sum(1).max())}")

def report(name, a, b, c, n, ref=None):
    rng = np.random.default_rng(1)
    r = a.shape[0]
    print(f"\n{name}: <{n}x{n}x{n}:{r}>, coefficients {sorted(set(np.unique(np.concatenate([a.ravel(), b.ravel(), c.ravel()]))))}")
    Ln = math.log(n)
    cl_amp = 0.5 * math.sqrt(n)
    best = {}
    for role, (x, y, z) in enumerate(((a, b, c), (b, c, a), (c, a, b))):
        t = to_LRP(x, y, z, n, rng)
        if t is None:
            print(f"  role {role}: NOT a valid algorithm in either convention"); continue
        f = factors(*t, n)
        for k in ("g_infinf", "g_inf2", "g_22", "g_2", "Q0", "amp"):
            best[k] = min(best.get(k, 1e99), f[k])
        print(f"  role {role}: g_infinf {f['g_infinf']:7.2f} (exp {math.log(f['g_infinf'])/Ln:.3f})  g_inf2 {f['g_inf2']:7.3f} (exp {math.log(f['g_inf2'])/Ln:.3f})  "
              f"g_22 {f['g_22']:7.2f}  g_2 {f['g_2']:7.2f} (exp {math.log(f['g_2'])/Ln:.3f})  Q0 {f['Q0']:3d}  amp {f['amp']:6.3f} (exp {math.log(f['amp']/cl_amp)/Ln:.3f})  "
              f"nnz {f['nnz']}  naive adds {f['adds']}  max row {f['maxrow']}")
    return best

def main():
    args = sys.argv[1:]
    n = int(args[args.index("--n") + 1]) if "--n" in args else 5
    name = args[args.index("--name") + 1] if "--name" in args else args[1]
    if args[0] == "exp":
        a, b, c = parse_exp(args[1], n)
    elif args[0] == "ae":
        a, b, c = parse_ae(args[1], args[2])
    elif args[0] == "sms":
        L, R, P = (parse_sms(f"{args[1]}_{s}.sms") for s in "LRP")
        a, b, c = L, R, P.T[:, np.array([n * j + i for i in range(n) for j in range(n)])]  # back to the (a, b, c) form
    report(name, a, b, c, n)

if __name__ == "__main__":
    main()
