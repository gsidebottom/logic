import glob, os, sys
SP = sys.argv[1]
os.environ.update(LNS_NAIVE="1", PLINOPT_BIN=f"{SP}/plinopt_main/bin", R48_SCRATCH=SP)
D = "/Users/greg/projects/logic/matmul/dps48"
sys.path.insert(0, f"{D}/patel"); sys.path.insert(0, D)
import sweep as SW
for w in sorted(glob.glob(f"{SP}/td/pcl2/work/*")):
    tag = os.path.basename(w); res = []
    for d in sorted(glob.glob(f"{w}/P_Pt_s*")):
        b = os.path.join(d, "best.slp")
        if not os.path.exists(b): res.append(None); continue
        try:
            c = SW.slpcheck(f"{SP}/td/pcl2/{tag}_P.sms", SW.transpose(SW.translate(b)))
            res.append(sum(c) if c else None)
        except Exception as e: res.append(None)
    ok = sorted(x for x in res if x is not None)
    print(f"{tag:14s} seeds with a program {len(ok)} of {len(res)}: best {ok[0] if ok else '-'}  all {ok}", flush=True)
