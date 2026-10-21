#!/usr/bin/env python3
"""Generate a Lean 4 / Mathlib correctness proof for a rank-r 4x4 scheme given
as three straight-line programs (named for the 201-operation scheme it certifies,
proof/Mm/Correct48_201.lean; PREFIX and --name make it reusable for any triple) (PLinOpt syntax: `t:=u+v;`, `t:=u-v;`,
`t:=u*2;`, `t:=u/2;`, output copies `oK:=name;`).

Statement: over ANY commutative ring `R` with an element `h` such that
`2 * h = 1` (so `h` is one half: Z[1/2]-algebras, every field of odd or zero
characteristic), the exact programs -- every operation is a hypothesis, a
halving `t:=u/2` being `t = u * h` -- compute the 16 entries of `A * B`.

Proof structure (keeps every `ring` goal small): for each wire a `have`
giving its value as a canonical linear form in the inputs with coefficients
`n * h^k` (closed by `ring`, or by `linear_combination e * h2` when halves
recombine; `e` is computed here by exact division by `2h - 1`), a `have` per
product, then each output by `linear_combination e_c * h2` on the expanded
bilinear identity.

Usage: lean_gen48_201.py PREFIX OUT.lean [--name Matmul48_201]   (PREFIX_{L,R,P}.slp)
"""
import re
import sys
from fractions import Fraction as Fr

sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import slp48check as C  # noqa: E402

RE_BIN = re.compile(r"^(-?)([A-Za-z_]\w*)([+-])([A-Za-z_]\w*)$")
RE_SCALE = re.compile(r"^(-?)([A-Za-z_]\w*)([*/])(\d+)$")
RE_COPY = re.compile(r"^(-?)([A-Za-z_]\w*)$")


# ----------------------------------------------------------------- h-polynomials
# a coefficient is a polynomial in h: dict power -> int
def hp_add(p, q, sign=1):
    r = dict(p)
    for k, v in q.items():
        r[k] = r.get(k, 0) + sign * v
    return {k: v for k, v in r.items() if v}


def hp_shift(p, s):
    return {k + s: v for k, v in p.items()}


def hp_scale(p, n):
    return {k: v * n for k, v in p.items() if v * n}


def hp_mul(p, q):
    r = {}
    for k1, v1 in p.items():
        for k2, v2 in q.items():
            r[k1 + k2] = r.get(k1 + k2, 0) + v1 * v2
    return {k: v for k, v in r.items() if v}


def hp_value(p):
    return sum(Fr(v, 2 ** k) for k, v in p.items())


def canonical(c):
    """the canonical h-polynomial of a rational c = n / 2^k."""
    c = Fr(c)
    if c == 0:
        return {}
    k = 0
    while c.denominator != 1:
        c *= 2
        k += 1
    assert c.denominator == 1
    return {k: int(c)}


def div_2h_minus_1(d):
    """exact quotient e with d(h) = (2h - 1) e(h); d must vanish at h = 1/2."""
    assert hp_value(d) == 0, d
    if not d:
        return {}
    n = max(d)
    coeffs = [d.get(k, 0) for k in range(n + 1)]
    # d = (h - 1/2) q;  q_n-1 = d_n, q_{k-1} = d_k + q_k / 2
    q = [Fr(0)] * n
    q[n - 1] = Fr(coeffs[n])
    for k in range(n - 1, 0, -1):
        q[k - 1] = coeffs[k] + q[k] / 2
    assert coeffs[0] + q[0] / 2 == 0
    e = {}
    for k, v in enumerate(q):
        v = v / 2
        assert v.denominator == 1, "non-integral quotient"
        if v:
            e[k] = int(v)
    return e


def lean_hpoly_times(p, var):
    """Lean term for (polynomial in h) * var, as a sum of monomials."""
    terms = []
    for k in sorted(p):
        n = p[k]
        hs = " * ".join(["h"] * k)
        core = " * ".join(x for x in [hs, var] if x)
        if n == 1:
            terms.append(core)
        elif n == -1:
            terms.append(f"-({core})")
        else:
            terms.append(f"({n}) * {core}")
    return terms


def lean_form(form, names):
    """form: dict var_index -> h-polynomial; names(i) -> Lean variable."""
    terms = []
    for i in sorted(form):
        terms += lean_hpoly_times(form[i], names(i))
    return " + ".join(terms) if terms else "0"


# ----------------------------------------------------------------- programs
class Side:
    def __init__(self, prog, n_in, in_name, prefix, integer_only):
        self.in_name, self.prefix = in_name, prefix
        self.env = {}       # program name -> (lean expr, form)  form: var -> hpoly
        self.wires = []     # (wire, hyp_name, hyp_rhs, form, proof_tactic)
        self.outputs = {}   # k -> (lean expr, form)
        self.raw = {}       # program name -> raw form (h-polynomials as computed, not canonical)
        self.outputs_raw = {}
        self.adds = self.scalings = 0
        n = 0
        for lhs, rhs in prog:
            rhs = rhs.replace(" ", "")
            is_out = re.fullmatch(r"o\d+", lhs) is not None
            m = RE_COPY.fullmatch(rhs)
            if m:
                assert m.group(1) == "", f"negated copy {lhs}:={rhs} (normalize first)"
                e, f = self.ref(m.group(2))
                self.raw[lhs] = self.raw_of(m.group(2))
                if is_out:
                    self.outputs[int(lhs[1:])] = (e, f)
                    self.outputs_raw[int(lhs[1:])] = self.raw[lhs]
                self.env[lhs] = (e, f)
                continue
            n += 1
            w = f"{prefix}{n}"
            m = RE_BIN.fullmatch(rhs)
            if m:
                assert m.group(1) == "", f"negated operand in {lhs}:={rhs} (normalize first)"
                self.adds += 1
                eu, fu = self.ref(m.group(2))
                ev, fv = self.ref(m.group(4))
                sg = 1 if m.group(3) == "+" else -1
                raw = {}
                for i in set(fu) | set(fv):
                    p = hp_add(fu.get(i, {}), fv.get(i, {}), sg)
                    if p:
                        raw[i] = p
                ru, rv = self.raw_of(m.group(2)), self.raw_of(m.group(4))
                rawraw = {}
                for i in set(ru) | set(rv):
                    p = hp_add(ru.get(i, {}), rv.get(i, {}), sg)
                    if p:
                        rawraw[i] = p
                hyp = f"{w} = {eu} {m.group(3)} {ev}"
                operands = [m.group(2), m.group(4)]
            else:
                m = RE_SCALE.fullmatch(rhs)
                assert m and m.group(1) == "", f"unsupported line {lhs}:={rhs}"
                self.scalings += 1
                eu, fu = self.ref(m.group(2))
                k = int(m.group(4))
                assert k in (2, 4), k
                s = {2: 1, 4: 2}[k]
                ru = self.raw_of(m.group(2))
                if m.group(3) == "*":
                    raw = {i: hp_scale(p, k) for i, p in fu.items()}
                    rawraw = {i: hp_scale(p, k) for i, p in ru.items()}
                    hyp = f"{w} = {eu} * {k}"
                else:
                    assert not integer_only, "halving on the P side"
                    raw = {i: hp_shift(p, s) for i, p in fu.items()}
                    rawraw = {i: hp_shift(p, s) for i, p in ru.items()}
                    hyp = f"{w} = {eu} * " + " * ".join(["h"] * s)
                operands = [m.group(2)]
            form = {i: canonical(hp_value(p)) for i, p in raw.items() if hp_value(p) != 0}
            # correction e with raw - form = (2h - 1) e, per variable
            corr = {}
            for i in set(raw) | set(form):
                d = hp_add(raw.get(i, {}), form.get(i, {}), -1)
                e = div_2h_minus_1(d)
                if e:
                    corr[i] = e
            rewrites = [f"h{w}"] + [self.env[o][2] for o in operands if o in self.env and self.env[o][2]]
            # text of the goal's left side after the rewrites (operands replaced by their forms)
            def text_of(o):
                return lean_form(self.env[o][1], in_name) if o in self.env and len(self.env[o]) == 3 else self.ref(o)[0]
            if len(operands) == 2:
                lhs_text = f"{text_of(operands[0])} {m.group(3)} {text_of(operands[1])}"
            else:
                lhs_text = None  # scalings never close by rfl (the form distributes the factor)
            canon_text = lean_form(form, in_name)
            # `rw` alone closes the goal only when the rewritten term IS the canonical
            # term: same text and the right operand a single term (a sum there would
            # associate differently from the left-nested canonical form)
            single_right = len(operands) == 2 and " + " not in text_of(operands[1])
            if corr:
                tactic = f"rw [{', '.join(rewrites)}]; linear_combination ({lean_form(corr, in_name)}) * h2"
            elif lhs_text == canon_text and single_right:
                tactic = f"rw [{', '.join(rewrites)}]"
            else:
                tactic = f"rw [{', '.join(rewrites)}]; ring"
            self.wires.append((w, f"h{w}", hyp, form, tactic))
            self.env[lhs] = (w, form, f"e{w}")
            self.raw[lhs] = rawraw
            if is_out:
                self.outputs[int(lhs[1:])] = (w, form)
                self.outputs_raw[int(lhs[1:])] = rawraw

    def raw_of(self, name):
        if name in self.raw:
            return self.raw[name]
        m = re.fullmatch(r"i(\d+)", name)
        assert m, f"undefined {name}"
        return {int(m.group(1)): {0: 1}}

    def ref(self, name):
        if name in self.env:
            return self.env[name][0], self.env[name][1]
        m = re.fullmatch(r"i(\d+)", name)
        assert m, f"undefined {name}"
        j = int(m.group(1))
        return self.in_name(j), {j: {0: 1}}

    def form_lemma(self, name):
        """the `e<wire>` lemma name of a program name, or None for inputs/copies of inputs."""
        if name in self.env and len(self.env[name]) == 3:
            return self.env[name][2]
        return None


def main():
    prefix, out = sys.argv[1], sys.argv[2]
    name = sys.argv[sys.argv.index("--name") + 1] if "--name" in sys.argv else "Matmul48_201"
    progs = {s: C.parse(open(f"{prefix}_{s}.slp").read()) for s in "LRP"}
    r = len(C.evaluate(progs["L"], 16)[0])
    aname = lambda j: f"a{j // 4}{j % 4}"  # noqa: E731
    bname = lambda j: f"b{j // 4}{j % 4}"  # noqa: E731
    mname = lambda k: f"m{k}"  # noqa: E731
    L = Side(progs["L"], 16, aname, "al", False)
    Rs = Side(progs["R"], 16, bname, "bl", False)
    P = Side(progs["P"], r, mname, "cl", True)
    assert set(L.outputs) == set(range(r)) and set(Rs.outputs) == set(range(r)) and set(P.outputs) == set(range(16))
    total = L.adds + L.scalings + Rs.adds + Rs.scalings + P.adds + P.scalings

    lines = []
    emit = lines.append
    # --- header
    emit(f"""/-
Copyright (c) 2026 Greg Sidebottom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Greg Sidebottom
-/
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# A {total}-operation rank-{r} scheme computes 4×4 matrix multiplication

Machine-checked correctness of a rank-{r} scheme for `4×4` matrix
multiplication with coefficients in `ℤ[1/2]`, whose three linear programs
use {L.adds + L.scalings} + {Rs.adds + Rs.scalings} + {P.adds + P.scalings} = {total} operations
({L.adds} + {Rs.adds} + {P.adds} additions/subtractions and {L.scalings} + {Rs.scalings} + {P.scalings} halvings;
copies are free).  Generated from
`matmul/dps48/cand48/{prefix.split('/')[-1]}_{{L,R,P}}.slp` by `matmul/dps48/lean_gen48_201.py`.

The statement is over an arbitrary **commutative ring** `R` with an
element `h` satisfying `2 * h = 1` -- i.e. any ring in which 2 is
invertible: `ℤ[1/2]`-algebras, and every field of characteristic ≠ 2.
The hypotheses are the exact straight-line programs: `al*` are the
{L.adds + L.scalings} operations forming the left factors (a halving `t := u/2` is
`t = u * h`), `bl*` the {Rs.adds + Rs.scalings} forming the right factors, `m*` the {r}
products (each with its `A`-factor on the left), `cl*` the {P.adds + P.scalings}
operations combining them.  Each wire is first shown equal to a canonical
linear form in the inputs (`ring`, or `linear_combination … * h2` where
halves recombine), then each of the 16 outputs equals `∑ₜ aᵢₜ bₜⱼ` by
`linear_combination` of `2 * h = 1` with a coefficient polynomial computed
by the generator (exact division by `2h - 1`).
-/

namespace {name}

variable {{R : Type _}} [CommRing R]
""")

    def wrap(words, first="    (", width=72):
        cont = " " * len(first)
        out_lines, cur, fresh = [], first, True
        for w in words:
            if len(cur) + len(w) + 1 > width and not fresh:
                out_lines.append(cur)
                cur, fresh = cont, True
            cur += ("" if fresh else " ") + w
            fresh = False
        out_lines.append(cur)
        return "\n".join(out_lines)

    emit("/-- Each of the 16 outputs equals the corresponding entry of `A * B`, in any\ncommutative ring where `2 * h = 1`. -/")
    emit("theorem correct (h : R) (h2 : 2 * h = 1)")
    emit(wrap([aname(j) for j in range(16)] + [bname(j) for j in range(16)], "    (").rstrip() + " : R)")
    allw = [w for w, *_ in L.wires] + [w for w, *_ in Rs.wires] + [mname(k) for k in range(r)] + [w for w, *_ in P.wires]
    emit(wrap(allw, "    (").rstrip() + " : R)")
    for side in (L, Rs):
        for w, hn, hyp, form, tac in side.wires:
            emit(f"    ({hn} : {hyp})")
    for k in range(r):
        emit(f"    (hm{k} : m{k} = {L.outputs[k][0]} * {Rs.outputs[k][0]})")
    for w, hn, hyp, form, tac in P.wires:
        emit(f"    ({hn} : {hyp})")
    goals = []
    for i in range(4):
        for j in range(4):
            rhs = " + ".join(f"{aname(4 * i + t)} * {bname(4 * t + j)}" for t in range(4))
            goals.append(f"{P.outputs[4 * i + j][0]} = {rhs}")
    emit("    :")
    emit("    " + (" ∧\n    ").join(goals) + " := by")
    # --- wire lemmas
    for side, names in ((L, aname), (Rs, bname)):
        for w, hn, hyp, form, tac in side.wires:
            emit(f"  have e{w} : {w} = {lean_form(form, names)} := by")
            emit(f"    {tac}")
    for w, hn, hyp, form, tac in P.wires:
        emit(f"  have e{w} : {w} = {lean_form(form, mname)} := by")
        emit(f"    {tac}")
    # --- products: m_k = (form L_k) * (form R_k)
    for k in range(r):
        eL, fL = L.outputs[k]
        eR, fR = Rs.outputs[k]
        rws = [f"hm{k}"]
        for side, e in ((L, eL), (Rs, eR)):
            lem = f"e{e}" if e.startswith(side.prefix) else None
            if lem:
                rws.append(lem)
        emit(f"  have pm{k} : m{k} = ({lean_form(fL, aname)}) * ({lean_form(fR, bname)}) := by")
        emit(f"    rw [{', '.join(rws)}]")
    # --- outputs
    emit("  refine ⟨" + ", ".join("?_" for _ in goals) + "⟩")
    for c in range(16):
        e_out, f_out = P.outputs[c]
        row, col = divmod(c, 4)
        # expand sum_k p_k F_k G_k into (i, j) -> h-polynomial
        bil = {}
        for k, pk in f_out.items():
            pk_int = pk.get(0, 0)
            assert set(pk) <= {0}, "P coefficients must be integers"
            for i, fi in L.outputs[k][1].items():
                for j, gj in Rs.outputs[k][1].items():
                    prod = hp_scale(hp_mul(fi, gj), pk_int)
                    bil[(i, j)] = hp_add(bil.get((i, j), {}), prod)
        corr_terms = []
        for i in range(16):
            for j in range(16):
                t = 1 if (i // 4 == row and i % 4 == j // 4 and j % 4 == col) else 0
                d = hp_add(bil.get((i, j), {}), {0: t}, -1)
                e = div_2h_minus_1(d)
                for term in lean_hpoly_times(e, f"{aname(i)} * {bname(j)}"):
                    corr_terms.append(term)
        rws = []
        if e_out.startswith("cl"):
            rws.append(f"e{e_out}")
        used = sorted(f_out) if e_out.startswith("cl") else [int(e_out[1:])]
        rws += [f"pm{k}" for k in used]
        emit(f"  · rw [{', '.join(rws)}]")
        if corr_terms:
            emit(f"    linear_combination ({' + '.join(corr_terms)}) * h2")
        else:
            emit("    ring")
    emit(f"\nend {name}\n")
    # wrap lines longer than Mathlib's 100-column linter limit at term boundaries
    def wrap_long(line, width=100):
        if len(line) <= width:
            return [line]
        indent = len(line) - len(line.lstrip(" "))
        cont = " " * (indent + 4)
        parts = []
        cur = ""
        # split on ' + ' (sums) or ', ' (rw lists), keeping the separator at the end of a chunk
        import re as _re
        tokens = _re.split(r"( \+ |, )", line)
        pieces = ["".join(tokens[i:i + 2]) for i in range(0, len(tokens), 2)]
        for piece in pieces:
            if cur and len(cur) + len(piece) > width:
                parts.append(cur.rstrip())
                cur = cont + piece
            else:
                cur += piece
        parts.append(cur.rstrip())
        return parts
    wrapped = []
    for line in "\n".join(lines).split("\n"):
        wrapped += wrap_long(line)
    open(out, "w").write("\n".join(wrapped))
    print(f"wrote {out}: L {L.adds}+{L.scalings}, R {Rs.adds}+{Rs.scalings}, P {P.adds}+{P.scalings}, total {total}; {len(L.wires) + len(Rs.wires) + len(P.wires)} wires, {r} products")


if __name__ == "__main__":
    main()
