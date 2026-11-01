#!/usr/bin/env python3
"""The two turned forms of a rank-48 scheme with its programs: [R; P^T K; K L^T] (o5, L's mode computes the outputs) and
[L K; P^T; R^T] (o6, R's mode does).  Programs come from the scheme's own by transposition (PLinOpt's transpozer) and
relabelling, so a turn costs nothing: cost(M^T) = cost(M) + rows - columns of M, here +32 on one side and -32 on another.
Every program is checked by SLPchecker against the turned matrix, every triple by slp48check on all 4096 equations.

  turned.py SMS_PREFIX SLP_PREFIX OUT_PREFIX      writes OUT_PREFIX_{o5,o6}_{L,R,P}.{sms,slp}
"""
import os, re, subprocess, sys
SP = "/private/tmp/claude-501/-Users-greg-projects-logic/fde6fc44-1302-4fb7-9f35-47e08b29f1c6/scratchpad"
os.environ.update(PLINOPT_BIN=f"{SP}/plinopt_main/bin", R48_SCRATCH=SP)
D = "/Users/greg/projects/logic/matmul/dps48"
sys.path.insert(0, f"{D}/patel"); sys.path.insert(0, D)
import sweep as SW
import lwh_family as F
import slp48check as C
sms, slp, out = sys.argv[1:4]
def k(m): return (m % 4) * 4 + m // 4
def tr(A): return [list(r) for r in zip(*A)]
def mk(M): return [[r[k(j)] for j in range(16)] for r in M]     # M K
def km(M): return [M[k(i)] for i in range(16)]                  # K M
def ren(text, tok): return re.sub(rf"\b{tok}(\d+)\b", lambda m: f"{tok}{k(int(m.group(1)))}", text)
L, R, P = (F.C_read(f"{sms}_{s}.sms") for s in "LRP")
pL, pR, pP = (SW.translate(f"{slp}_{s}.slp") for s in "LRP")
tL, tR, tP = (SW.transpose(x) for x in (pL, pR, pP))
SETS = {"o5": ((R, mk(tr(P)), km(tr(L))), (pR, ren(tP, "i"), ren(tL, "o"))),
        "o6": ((mk(L), tr(P), tr(R)), (ren(pL, "i"), tP, tR))}
for name, (Ms, Ps) in SETS.items():
    pre = f"{out}_{name}"
    cnt = []
    for s, M, prog in zip("LRP", Ms, Ps):
        F.write_sms(f"{pre}_{s}.sms", M)
        open(f"{pre}_{s}.slp", "w").write(prog)
        c = SW.slpcheck(f"{pre}_{s}.sms", prog)
        assert c, (name, s)
        cnt.append(c)
    o = subprocess.run([sys.executable, "-I", f"{D}/slp48check.py", pre], capture_output=True, text=True)
    assert o.returncode == 0 and "failing: 0 / 4096" in o.stdout, o.stdout + o.stderr
    print(f"{os.path.basename(out)} {name}: L {cnt[0]}, R {cnt[1]}, P {cnt[2]}, total {sum(sum(c) for c in cnt)}, Brent 0 of 4096", flush=True)
