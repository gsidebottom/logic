import json, sys, time
src = open(sys.argv[2]).read()
exec(src[:src.index('rng = np.random')])
np.set_printoptions(precision=5, suppress=True, linewidth=120)
rng = np.random.default_rng(7); t0 = time.time(); got = []
while time.time() - t0 < 70 and len(got) < 3:
    res = minimize(f, rng.normal(size=18) * 2, args=('all',), method='L-BFGS-B', options=dict(maxiter=500, ftol=1e-14, gtol=1e-9))
    if -res.fun > 767.99: got.append(res.x)
print(len(got), "solutions at the bound in", round(time.time() - t0), "s")
mono = lambda g: np.all(np.sum(np.abs(g) > 1e-5, 0) == 1) and np.all(np.sum(np.abs(g) > 1e-5, 1) == 1)
for x in got[:1]:
    A, B, C = expm(skew(x[:6])), expm(skew(x[6:12])), expm(skew(x[12:]))
    print("fourth-power sum", -f(x, 'all'))
    n = sum(mono(A @ g @ A.T) and mono(B @ h @ B.T) and mono(C @ k @ C.T) for g, h, k in ids) + sum(mono(A @ g @ C.T) and mono(B @ h @ B.T) and mono(C @ k @ A.T) for g, h, k in sl)
    print("elements acting by signed permutations:", n, "of", len(ids) + len(sl))
    for nme, Q in (("A", A), ("B", B), ("C", C)):
        print(nme); print(Q)
        print("  distinct |entries|:", sorted(set(np.round(np.abs(Q).ravel(), 4).tolist())))
    np.save(sys.argv[3], np.array([A, B, C]))
