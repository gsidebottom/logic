#!/usr/bin/env python3
"""Negative gate for the subgame checker: tampered certificates must be
REJECTED. Takes a valid certificate, (1) inflates the root's claimed
value, (2) inflates a leaf's claimed value, and asserts the checker
fails on both. A checker that accepts a tamper is broken.

  python3 matmul/r22/subgame_tamper_test.py CERT.json
"""
import json, subprocess, sys, os, tempfile

def main(path):
    base = json.load(open(path))
    ok = True
    with tempfile.TemporaryDirectory() as td:
        t1 = json.loads(json.dumps(base))
        for nd in t1["nodes"]:
            if nd["key"] == t1["root"]:
                nd["value"] += 1
        t2 = json.loads(json.dumps(base))
        leaf = next(nd for nd in t2["nodes"] if nd["choice"] == 0)
        leaf["value"] += 1
        for name, cert in (("root+1", t1), ("leaf+1", t2)):
            p = os.path.join(td, "t.json")
            json.dump(cert, open(p, "w"))
            r = subprocess.run(
                [sys.executable, os.path.join(os.path.dirname(__file__), "subgame_verify.py"), p],
                capture_output=True, text=True)
            if r.returncode == 0:
                print(f"TAMPER {name}: ACCEPTED — CHECKER IS BROKEN")
                ok = False
            else:
                print(f"tamper {name}: rejected ok")
    sys.exit(0 if ok else 1)

if __name__ == "__main__":
    main(sys.argv[1])
