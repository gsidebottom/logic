import glob, os, shutil, subprocess, sys
SP = sys.argv[1]
os.environ.update(LNS_NAIVE="1", PLINOPT_BIN=f"{SP}/plinopt_main/bin", R48_SCRATCH=SP)
D = "/Users/greg/projects/logic/matmul/dps48"
sys.path.insert(0, f"{D}/patel"); sys.path.insert(0, D)
import sweep as SW
sms = f"{SP}/plinopt_main/data/4x4x4_48_accurate_262_R.sms"
os.makedirs(f"{SP}/td/r76", exist_ok=True); args = []
for d in sorted(glob.glob(f"{SP}/td/seeded/a262/S_R_s*")):
    t = SW.translate(os.path.join(d, "best.slp")); c = SW.slpcheck(sms, t); s = os.path.basename(d).split('_')[-1]
    if not c or sum(c) > 76: continue
    pre = f"{SP}/td/r76/{s}"
    open(pre + "_R.slp", "w").write(t)
    for m in "LP": shutil.copy(f"{SP}/plinopt_main/data/4x4x4_48_accurate_262_{m}.slp", pre + f"_{m}.slp")
    args += [f"{s}<{c[0]},{c[1]}>", pre]
print(subprocess.run([f"/Users/greg/projects/logic/target/release/slpopt", "model", "published", f"{SP}/plinopt_main/data/4x4x4_48_accurate_262"] + args, capture_output=True, text=True).stdout)
