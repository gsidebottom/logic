#!/usr/bin/env python3
"""Per-level metrics of fused levels for every matrix multiplication scheme on disk, any shape.

A level <g1 x g2 x g3 : r> on an (M x K)(K x N) product splits A into g1 x g2 blocks, B into
g2 x g3, C into g1 x g3, computes r block products and costs three fused passes.  Per level:
  saving   = r / (g1 g2 g3)                       products kept (0.75 for <4x4x4:48>)
  streams  = g1 g2 + r, g2 g3 + r, g1 g3 + r      blocks read and written by the L, R, P passes
                                                   (64/64/64 for 4x4:48; above about 64 the
                                                   passes lose bandwidth: 118 ran at 50-70%)
  traffic  = 3 + r (1/(g1 g2) + 1/(g2 g3) + 1/(g1 g3))   pass bytes per level in units of n^2
                                                   words on a square n problem (12 for 4x4:48)
  amp      = max_j (1/2) sqrt(sum_i p_ji^2 |L_i|^2 |R_i|^2), normalized by the classical
             algorithm's (1/2) sqrt(g2); gamma_inf2 normalized by g2 (the classical value)
  *_eq     = the normalized factor raised to ln(0.75)/ln(saving): the growth per 4x4:48-level
             worth of saving, directly comparable with accurate_262's 2.828 (amp) and 5.657.
Representatives only (no orbit optimization), except that Kronecker composites of accurate
pieces are formed explicitly.   python3 -I levels.py OUT.csv
"""
import ast, csv, math, os, re, sys
if sys.flags.isolated:
    sys.path.append("/Users/greg/Library/Python/3.9/lib/python/site-packages")
import numpy as np

REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
HB = f"{REPO}/matmul/out/scratch_backup_2026-10-22/hellsbells/repo/algorithms/other"
PL = f"{REPO}/matmul/dps48/plinopt/data"

def parse_exp(path, shape):
    g1, g2, g3 = shape
    term = re.compile(r"([+-]?)(\d*)\*?([abc])(\d)(\d)")
    rows = []
    for line in open(path):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        parts = line.split(")*(")
        assert len(parts) == 3, line
        vecs = []
        for part, letter in zip(parts, "abc"):
            d = {}
            s = part.strip("()")
            pos = 0
            for m in term.finditer(s):
                assert m.group(3) == letter, (path, line)
                c = (-1.0 if m.group(1) == "-" else 1.0) * (float(m.group(2)) if m.group(2) else 1.0)
                d[(int(m.group(4)), int(m.group(5)))] = d.get((int(m.group(4)), int(m.group(5))), 0) + c
                pos = m.end()
            assert s[pos:].strip() == "", (path, line)
            vecs.append(d)
        rows.append(vecs)
    r = len(rows)
    a = np.zeros((r, g1 * g2)); b = np.zeros((r, g2 * g3)); c_ki = np.zeros((r, g1 * g3)); c_ik = np.zeros((r, g1 * g3))
    for t, (da, db, dc) in enumerate(rows):
        for (i, j), v in da.items(): a[t, (i - 1) * g2 + j - 1] += v
        for (j, k), v in db.items(): b[t, (j - 1) * g3 + k - 1] += v
        for (x, y), v in dc.items():
            if x <= g3 and y <= g1: c_ki[t, (y - 1) * g3 + x - 1] += v      # c_ki -> C[i][k]
            if x <= g1 and y <= g3: c_ik[t, (x - 1) * g3 + y - 1] += v      # c_ik -> C[i][k]
    return a, b, (c_ki.T, c_ik.T)

def parse_ae(path, func, shape):
    g1, g2, g3 = shape
    tree = ast.parse(open(path).read())
    fn = next(nd for nd in ast.walk(tree) if isinstance(nd, ast.FunctionDef) and nd.name == func)
    arrays = [ast.literal_eval(nd.args[0]) for nd in ast.walk(fn) if isinstance(nd, ast.Call) and getattr(nd.func, "attr", "") == "array"]
    U, V, W = (np.array(x, complex) for x in arrays)    # (n m, r), (m p, r), (p n, r), rows i*m+j, j*p+k, k*n+i
    if max(abs(X.imag).max() for X in (U, V, W)) > 0:
        return None                                      # a complex scheme (the rank-48 4x4): not for real arithmetic
    U, V, W = (X.real for X in (U, V, W))
    T = np.array([k * g1 + i for i in range(g1) for k in range(g3)])
    return U.T, V.T, (W[T, :],)

def parse_sms(path):
    """PLinOpt .sms; DPS's accurate 2x2x2 files write 1013 as a placeholder for sqrt(3) (header comment)"""
    sqrt3 = False
    with open(path) as f:
        head = f.readline()
        while head.startswith("#"):
            sqrt3 |= "1013 is a placeholder for sqrt(3)" in head
            head = f.readline()
        r, c, _ = head.split()
        M = np.zeros((int(r), int(c)))
        for line in f:
            t = line.split()
            if len(t) < 3 or t[0] == "0":
                break
            v = t[2]
            num, den = (v.split("/") + ["1"])[:2]
            num, den = float(num), float(den)
            if sqrt3:                                    # num = a + b * 1013 with small a: b sqrt(3) + a
                b = round(num / 1013); a = num - 1013 * b
                assert abs(a) <= 10, (path, v)
                num = a + b * 3 ** 0.5
            M[int(t[0]) - 1, int(t[1]) - 1] = num / den
    return M

def check(L, R, P, shape, rng, trials=4):
    g1, g2, g3 = shape
    for _ in range(trials):
        A = rng.integers(-3, 4, (g1, g2)).astype(float); B = rng.integers(-3, 4, (g2, g3)).astype(float)
        if not np.allclose(P @ ((L @ A.reshape(-1)) * (R @ B.reshape(-1))), (A @ B).reshape(-1)):
            return False
    return True

def metrics(L, R, P, shape):
    g1, g2, g3 = shape
    r = L.shape[0]
    l2, r2 = np.linalg.norm(L, axis=1), np.linalg.norm(R, axis=1)
    s2 = np.abs(P) @ (l2 * r2)
    sinf = np.abs(P) @ (np.abs(L).sum(1) * np.abs(R).sum(1))
    amp = (0.5 * np.sqrt((P ** 2) @ (l2 ** 2 * r2 ** 2))).max()
    nz = P != 0
    nnzL, nnzR = (L != 0).sum(1), (R != 0).sum(1)
    q0 = max(int(nz[j].sum()) + int(max(nnzL[i] + nnzR[i] for i in np.nonzero(nz[j])[0])) for j in range(P.shape[0]))
    saving = r / (g1 * g2 * g3)
    k = math.log(0.75) / math.log(saving)
    amp_ratio = amp / (0.5 * math.sqrt(g2)); g_ratio = s2.max() / g2
    return dict(r=r, saving=round(saving, 4), streams=f"{g1*g2+r}/{g2*g3+r}/{g1*g3+r}", max_streams=max(g1 * g2, g2 * g3, g1 * g3) + r,
                traffic=round(3 + r * (1 / (g1 * g2) + 1 / (g2 * g3) + 1 / (g1 * g3)), 2),
                amp=round(float(amp), 3), amp_ratio=round(amp_ratio, 3), amp_eq=round(amp_ratio ** k, 3),
                g_inf2=round(float(s2.max()), 2), g_ratio=round(g_ratio, 3), g_eq=round(g_ratio ** k, 3),
                g_infinf=round(float(sinf.max()), 1), Q0=q0, nnz=int((L != 0).sum() + (R != 0).sum() + nz.sum()),
                coeffs=len(np.unique(np.abs(np.concatenate([L.ravel(), R.ravel(), P.ravel()])))) - 1)

def kron_scheme(S, T):
    (L1, R1, P1, sh1), (L2, R2, P2, sh2) = S, T
    return np.kron(L1, L2), np.kron(R1, R2), np.kron(P1, P2), tuple(a * b for a, b in zip(sh1, sh2))

def main():
    out = sys.argv[1]
    rng = np.random.default_rng(1)
    items = []   # (name, source, shape, L, R, P)
    def add(name, source, shape, L, R, Ps, verify=True):
        for P in Ps:
            if not verify or check(L, R, P, shape, rng):
                items.append((name, source, shape, L, R, P)); return
        print(f"  !! {name}: no convention verified", file=sys.stderr)
    # AlphaEvolve (google-deepmind/alphaevolve_results, Apache 2.0), via the Hell's Bells copy
    AE = f"{HB}/unsorted/misc/AlphaEvolveSchemes.py.txt"
    for s in ("245", "247", "248", "256", "333", "346", "347", "348", "356", "357", "444", "445", "447", "456", "555"):
        shape = tuple(int(ch) for ch in s)
        parsed = parse_ae(AE, f"decomposition_{s}", shape)
        if parsed is None:
            print(f"  -- AlphaEvolve-{s}: complex coefficients, skipped", file=sys.stderr); continue
        L, R, Ps = parsed
        add(f"AlphaEvolve-{s}", "alphaevolve", shape, L, R, Ps)
    # Kauers-Wood / Kemper (mod0 = over Z), Moosbauer-Poole(-Kemper) 5x5 and 6x6
    import glob
    for path in sorted(glob.glob(f"{HB}/unsorted/kauerswood/*/*-mod0.exp") + glob.glob(f"{HB}/unsorted/misc/MoosbauerPooleKemper-*-mod0.exp")):
        base = os.path.basename(path)[:-9]
        m = re.search(r"-(\d)(\d)(\d)-(\d+)$", base)
        shape = (int(m.group(1)), int(m.group(2)), int(m.group(3)))
        L, R, Ps = parse_exp(path, shape)
        add(base, "kauers-wood" if "Kauers" in base else "kemper" if "Kemper" in base else "moosbauer-poole", shape, L, R, Ps)
    # PLinOpt data (DPS and others), already in our convention
    for prefix, shape in (("2x2x2_7_Strassen", (2, 2, 2)), ("2x2x2_7_Winograd", (2, 2, 2)), ("2x2x2_7_DPS-accurate", (2, 2, 2)),
                          ("2x2x2_7_DPS-evenpow-12.2034", (2, 2, 2)),   # DPS24 Eq. (38), dyadic: the library's SW level since 2026-11-02
                          ("2x2x2_7_DPS-integral-12.0662", (2, 2, 2)), ("2x2x2_7_DPS-smallrat-12.2034", (2, 2, 2)),
                          ("3x3x3_23_55", (3, 3, 3)), ("3x3x3_23_58", (3, 3, 3)), ("3x3x3_23_Grey-221", (3, 3, 3)), ("3x3x3_JS", (3, 3, 3)),
                          ("3x3x6_40", (3, 3, 6)), ("3x3x6_40_DPS-accurate", (3, 3, 6)), ("3x6x3_40", (3, 6, 3)), ("3x6x3_40_DPS-accurate", (3, 6, 3)),
                          ("6x3x3_40", (6, 3, 3)), ("6x3x3_40_DPS-accurate", (6, 3, 3)), ("6x3x3_40_Smirnov", (6, 3, 3)),
                          ("3x4x7_63_rational", (3, 4, 7)), ("4x4x4_48_accurate_262", (4, 4, 4)), ("4x4x4_48_rational", (4, 4, 4)), ("4x4x4_49_156", (4, 4, 4))):
        try:
            L, R, P = (parse_sms(f"{PL}/{prefix}_{s}.sms") for s in "LRP")
        except FileNotFoundError as e:
            print(f"  !! {prefix}: {e}", file=sys.stderr); continue
        add(prefix, "plinopt", shape, L, R, (P,))
    # Kronecker composites of accurate pieces
    byname = {it[0]: (it[3], it[4], it[5], it[2]) for it in items}
    for a, b in (("2x2x2_7_DPS-accurate", "2x2x2_7_DPS-accurate"), ("2x2x2_7_Strassen", "2x2x2_7_Strassen"), ("2x2x2_7_Winograd", "2x2x2_7_Winograd"),
                 ("2x2x2_7_DPS-accurate", "3x3x6_40_DPS-accurate"), ("2x2x2_7_DPS-accurate", "4x4x4_48_accurate_262"), ("3x3x6_40_DPS-accurate", "3x3x6_40_DPS-accurate")):
        if a in byname and b in byname:
            L, R, P, shape = kron_scheme(byname[a], byname[b])
            add(f"{a} (x) {b}", "kronecker", shape, L, R, (P,), verify=False)   # valid up to the block index order, which the metrics ignore
    rows = []
    for name, source, shape, L, R, P in items:
        m = metrics(L, R, P, shape)
        rows.append(dict(name=name, source=source, shape="x".join(map(str, shape)), **m))
    with open(out, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys())); w.writeheader(); w.writerows(rows)
    rows.sort(key=lambda d: (d["saving"], d["amp_eq"]))
    print(f"{'scheme':42s} {'shape':7s} {'r':>4s} {'saving':>6s} {'streams L/R/P':>14s} {'traffic':>7s} {'amp':>6s} {'amp/cl':>6s} {'amp_eq':>6s} {'g_inf2':>7s} {'g_eq':>6s} {'Q0':>3s} {'coef':>4s}")
    for d in rows:
        print(f"{d['name'][:42]:42s} {d['shape']:7s} {d['r']:4d} {d['saving']:6.3f} {d['streams']:>14s} {d['traffic']:7.2f} {d['amp']:6.3f} {d['amp_ratio']:6.3f} {d['amp_eq']:6.3f} {d['g_inf2']:7.2f} {d['g_eq']:6.3f} {d['Q0']:3d} {d['coeffs']:4d}")
    print("\nreference: accurate_262 <4x4x4:48> saving 0.750, streams 64/64/64, traffic 12.0, amp 2.828 (amp/cl 2.828, amp_eq 2.828), gamma_inf2 22.63 (g_eq 5.657)")

if __name__ == "__main__":
    main()
