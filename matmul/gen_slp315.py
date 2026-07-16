#!/usr/bin/env python3
"""Regenerate Rust SLP modules from PLinOpt data-dir SLP triples.
Usage: gen_slp315.py [base] [outprefix]
  base       data-dir triple base name (default 4x4x4_48_rational)
  outprefix  src/<outprefix>.rs scalar + src/<outprefix>g.rs generic
Defaults regenerate the original slp315 pair; run with
  gen_slp315.py 4x4x4_48_accurate slp284
for the 284-op accurate triple (checker: <80,4>+<68,8>+<108,16>).
/2^k becomes fmul by INV2POW[k] (scalar) or scale2(-k) (generic).
Reuses shiftmin's expression parser."""
import sys

sys.path.insert(0, 'matmul/dps48')
from shiftmin import parse

BASE = sys.argv[1] if len(sys.argv) > 1 else "4x4x4_48_rational"
PRE = sys.argv[2] if len(sys.argv) > 2 else "slp315"
# BASE containing '/' is a path prefix (…/ours -> …/ours_L.slp);
# otherwise it names a data-dir triple.
D = "matmul/dps48/plinopt/data"
PATH = BASE if "/" in BASE else f"{D}/{BASE}"


def emit_delayed_p(name, slp_path):
    """P network over unreduced (lo, hi) pairs: products enter as the
    two 64-bit halves of the 128-bit core products; wires accumulate
    in u128 limb-sums; x2^k shifts both limbs; subtraction adds the
    negated pair via  -v = (KL*2^64 - lo) + 2^64*(KL*p - hi - KL)
    (adds KL*2^64*p = 0 mod p), with KL chosen PER SITE from static
    bound tracking so limbs never underflow; outputs pay one combine
    reduce(lo) + reduce(hi)*2^64 mod p. Generator asserts every limb
    bound < 2^127."""
    P_ = 0xFFFF_FFFF_0000_0001
    ops = parse(slp_path)
    lines = [
        f"pub fn {name}(plo: &[u64; 48], phi: &[u64; 48], out: &mut [u64; 16]) {{",
    ]
    defined = {"0": ("0u128", "0u128")}
    bounds = {"0": (0, 0)}
    for i in range(48):
        defined[f"i{i}"] = (f"(plo[{i}] as u128)", f"(phi[{i}] as u128)")
        bounds[f"i{i}"] = ((1 << 64) - 1, P_ - 1)  # product limb bounds
    tmp = 0
    for nm, terms in ops:
        lo_expr, hi_expr = None, None
        blo, bhi = 0, 0
        for (s_, src, k) in terms:
            slo, shi = defined[src]
            tlo, thi = bounds[src]
            if k > 0:
                slo, shi = f"({slo} << {k})", f"({shi} << {k})"
                tlo, thi = tlo << k, thi << k
            elif k < 0:
                raise ValueError(f"halving in delayed P: {nm}")
            if s_ < 0:
                kl = 1
                while kl * (1 << 64) < tlo or kl * (P_ - 1) < thi + kl:
                    kl *= 2
                neg_lo = kl << 64
                neg_hi = kl * P_ - kl
                slo = f"({neg_lo:#x}u128 - {slo})"
                shi = f"({neg_hi:#x}u128 - {shi})"
                tlo, thi = neg_lo, neg_hi
            if lo_expr is None:
                lo_expr, hi_expr = slo, shi
            else:
                lo_expr = f"{lo_expr} + {slo}"
                hi_expr = f"{hi_expr} + {shi}"
            blo += tlo
            bhi += thi
        assert blo < (1 << 127) and bhi < (1 << 127), f"limb bound blown at {nm}"
        v = f"t{tmp}"
        tmp += 1
        lines.append(f"    let {v}_lo: u128 = {lo_expr};")
        lines.append(f"    let {v}_hi: u128 = {hi_expr};")
        defined[nm] = (f"{v}_lo", f"{v}_hi")
        bounds[nm] = (blo, bhi)
        if nm.startswith("o"):
            lines.append(
                f"    out[{nm[1:]}] = fadd(reduce128({v}_lo), "
                f"fmul(reduce128({v}_hi), TWO64_MOD_P));"
            )
    lines.append("}")
    return "\n".join(lines)


def emit_scalar(name, slp_path, n_in, n_out):
    ops = parse(slp_path)
    lines = [f"pub fn {name}(inp: &[u64; {n_in}], out: &mut [u64; {n_out}]) {{"]
    defined = {f"i{i}": f"inp[{i}]" for i in range(n_in)}
    defined["0"] = "0"
    tmp = 0
    for nm, terms in ops:
        expr = None
        for (s, src, k) in terms:
            ref = defined[src]
            piece = ref
            if k > 0:
                piece = f"fmul({ref}, {2**k})"
            elif k < 0:
                piece = f"fmul({ref}, INV2POW[{-k}])"
            if expr is None:
                expr = piece if s > 0 else f"fneg({piece})"
            else:
                expr = f"fadd({expr}, {piece})" if s > 0 else f"fsub({expr}, {piece})"
        v = f"t{tmp}"
        tmp += 1
        lines.append(f"    let {v} = {expr};")
        defined[nm] = v
        if nm.startswith("o"):
            lines.append(f"    out[{nm[1:]}] = {v};")
    lines.append("}")
    return "\n".join(lines)


def emit_generic(name, slp_path, n_in, n_out):
    ops = parse(slp_path)
    lines = [f"pub fn {name}<T: El>(inp: &[T], out: &mut [T]) {{"]
    defined = {f"i{i}": f"inp[{i}]" for i in range(n_in)}
    lines.append("    let zz = inp[0].sub(&inp[0]);")
    defined["0"] = "zz"
    tmp = 0
    for nm, terms in ops:
        expr = None
        for (s, src, k) in terms:
            ref = defined[src]
            piece = f"{ref}.scale2({k})" if k else None
            if expr is None:
                first = piece if piece else f"{ref}.clone()"
                expr = first if s > 0 else f"{first}.neg()"
            else:
                arg = piece if piece else ref
                op = "add" if s > 0 else "sub"
                expr = f"{expr}.{op}(&{arg})"
        v = f"t{tmp}"
        tmp += 1
        lines.append(f"    let {v} = {expr};")
        defined[nm] = v
        if nm.startswith("o"):
            lines.append(f"    out[{nm[1:]}] = {v}.clone();")
    lines.append("}")
    return "\n".join(lines)


hdr_s = f"""// AUTO-GENERATED by matmul/gen_slp315.py from PLinOpt data-dir SLPs
// (triple {BASE}).
"""
src = hdr_s
src += emit_scalar("slp_l", f"{PATH}_L.slp", 16, 48) + "\n\n"
src += emit_scalar("slp_r", f"{PATH}_R.slp", 16, 48) + "\n\n"
src += emit_scalar("slp_p", f"{PATH}_P.slp", 48, 16) + "\n"
try:
    src += "\n" + emit_delayed_p("dslp_p", f"{PATH}_P.slp") + "\n"
except ValueError as e:
    print(f"note: no delayed P emitted ({e})")
open(f"src/{PRE}.rs", "w").write(src)

hdr_g = f"""// AUTO-GENERATED by matmul/gen_slp315.py (generic variant) from the
// PLinOpt data-dir SLP triple {BASE}. El is any Goldilocks-
// element-like type: u64 scalars or matrix blocks.
"""
src = hdr_g
src += emit_generic("gslp_l", f"{PATH}_L.slp", 16, 48) + "\n\n"
src += emit_generic("gslp_r", f"{PATH}_R.slp", 16, 48) + "\n\n"
src += emit_generic("gslp_p", f"{PATH}_P.slp", 48, 16) + "\n"
open(f"src/{PRE}g.rs", "w").write(src)
print(f"src/{PRE}.rs + src/{PRE}g.rs regenerated from {BASE}")
