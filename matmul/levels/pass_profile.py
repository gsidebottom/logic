"""Where a plan's time goes, from the calibration (matmul/fastmm/results/calib5_*.txt): per level and product
shape, the three passes (seconds, GB/s of the words they move), the GEMM-only time of a sub-problem at the
best stream count, and the best pipelined steady time; steady/gemm-only is what hiding the passes behind the
GEMMs costs, passes/gemm-only what they cost unhidden.  2026-11-14."""
import sys, re, collections
R = {'SW':7,'D48':48,'R336':40,'R363':40,'R633':40}
G = {'SW':(2,2,2),'D48':(4,4,4),'R336':(3,3,6),'R363':(3,6,3),'R633':(6,3,3)}
for prec, w in (('f32',4),('f64',8)):
    c = {}
    for line in open('../fastmm/results/calib5_%s.txt' % prec):
        if line[0] == '#': continue
        k, m, kk, n, t = line.split(); c[(k, int(m), int(kk), int(n))] = float(t)
    print('==', prec, ' level  product-shape | passes s  GB/s | best GEMM-only per subproblem (k) TF | best pipelined steady (cfg) | steady/gemm-only | passes/gemm-only')
    for (k, m, kk, n), t in sorted(c.items(), key=lambda x: (x[0][0], x[0][1]*x[0][2]*x[0][3])):
        if k not in R: continue
        g = G[k]; r = R[k]
        words = (g[0]*g[1]+r)*m*kk + (g[1]*g[2]+r)*kk*n + (g[0]*g[2]+r)*m*n
        gm = min((c[(q, m, kk, n)], q) for q in ('G'+k, 'G3'+k, 'G4'+k, 'G6'+k) if (q, m, kk, n) in c)
        fl = 2.0*m*kk*n
        best = None
        for st in (3, 6):
            for p in (2, 3, 4):
                key = ('P%sk%dp%ds' % (k, st, p), m, kk, n)
                if key in c and (best is None or c[key] < best[0]): best = (c[key], 'k%dp%d' % (st, p))
        s = '%-5s %5dx%5dx%5d | %8.5f %6.1f | %9.5f (%s) %.3f TF |' % (k, m, kk, n, t, words*w/t/1e9, r*gm[0], gm[1], fl/gm[0]/1e12)
        if best: s += ' %9.5f (%s) %.3f TF | %.3f | %.3f' % (best[0], best[1], r*fl/best[0]/1e12, best[0]/(r*gm[0]), t/(r*gm[0]))
        print(s)
