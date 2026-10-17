#!/usr/bin/env python3
"""Stage a Zenodo deposit from a git ref, so every uploaded file matches
the tagged repository state exactly (git archive / git show; never the
working tree).

  zenodo_stage.py ks51 REF LABEL   -> zenodo-upload-ks51-LABEL/
  zenodo_stage.py mm55 REF LABEL   -> zenodo-upload-mm55-LABEL/

REF is the deposit tag (HEAD for a preview); LABEL names the version
(e.g. v2.0).  Prints each staged file with its size.
"""
import pathlib
import shutil
import subprocess
import sys

kind, ref, label = sys.argv[1:4]
root = pathlib.Path(__file__).resolve().parent.parent
out = root / f"zenodo-upload-{kind}-{label}"
if out.exists():
    shutil.rmtree(out)
out.mkdir()


def show(path, dest):
    data = subprocess.run(["git", "show", f"{ref}:{path}"], cwd=root,
                          capture_output=True, check=True).stdout
    (out / dest).write_bytes(data)


def archive(dest, paths, fmt="tar.gz", prefix=None):
    cmd = ["git", "archive", f"--format={fmt}", "-o", str(out / dest)]
    if prefix:
        cmd.append(f"--prefix={prefix}")
    cmd.append(ref)
    cmd += paths
    subprocess.run(cmd, cwd=root, check=True)


if kind == "ks51":
    show("doc/matmul_3x3_rank23_add51.pdf", "matmul_3x3_rank23_add51.pdf")
    show("proof/Mm/Ring51.lean", "Ring51.lean")
    show("proof/Mm/SP51.lean", "SP51.lean")
    archive("proof-lake-project.zip", ["proof"], fmt="zip")
    archive("ks51-certificates.tar.gz", [
        "matmul/external/ks51", "matmul/external/sp51",
        "matmul/external/flat55"])
    archive("ks51-tools.tar.gz", [
        "src/bin/fbmin.rs", "src/bin/fbsmin.rs", "src/bin/floors.rs",
        "src/floors.rs", "src/bin/symenum.rs", "src/flip.rs",
        "src/bin/flip.rs", "matmul/fbsweep.py", "matmul/fbsweep2.py",
        "matmul/fbsloop.py", "matmul/modelconv.py",
        "matmul/gen_ring51_lean.py", "matmul/gen_sp51_lean.py",
        "matmul/gaugecanon.py", "matmul/lift.py", "matmul/equiv.py",
        "matmul/brent.py", "matmul/cfloor.py", "matmul/gf2min.py",
        "matmul/flat55_frontier.py", "matmul/symorbits.py",
        "matmul/symcnf.py", "matmul/symenumd.py", "matmul/symshape.py"])
elif kind == "mm55":
    show("doc/matmul_adds_paper.pdf", "matmul_adds_paper.pdf")
    show("matmul/external/i19-55adds-slp.txt", "i19-55adds-slp.txt")
    show("matmul/external/i19-perminov56.bits", "i19-perminov56.bits")
    show("matmul/verify_slp_file.py", "verify_slp_file.py")
    show("src/mm55.rs", "mm55.rs")
    archive("proof-lake-project.zip", ["proof"], fmt="zip")
    archive("flat55-frontier.tar.gz", [
        "matmul/external/flat55", "src/floors.rs", "src/bin/floors.rs",
        "matmul/cfloor.py", "matmul/gf2min.py",
        "matmul/flat55_frontier.py"])
else:
    sys.exit("kind must be ks51 or mm55")

archive(f"logic-{kind}-{label}.tar.gz", [], prefix=f"logic-{kind}-{label}/")

print(f"staged {out.relative_to(root)}/ from {ref}:")
for f in sorted(out.iterdir()):
    print(f"  {f.name:42s} {f.stat().st_size / 1e6:8.2f} MB")
