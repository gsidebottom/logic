#!/usr/bin/env python3
"""Generate a k-bit ripple-carry adder check `a + b + c_in = s` in two forms:

  <out>.cnf        fully expanded (17 clauses per full adder: the five
                   definitional equations of lib/adder.jq, Tseitin-style)
  <out>.res.cnf    residual only (the input/output unit constraints)
  <out>.boxes.json k compiled full_adder instances over (a_i, b_i, c_i, s_i, c_i+1)

Variables: a_i = i+1, b_i = k+i+1, c_i = 2k+i+1 (i = 0..k), s_i = 3k+i+2;
internals u_i v_i w_i follow (expanded form only).

Usage: gen_adder_boxes.py K A B CIN S OUT [MAXBITS]
  A, B, S may be "free"; MAXBITS forces the bits >= MAXBITS of a and b to 0
"""
import json, sys

def main():
    k, a, b, cin, s, out = int(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5], sys.argv[6]
    maxbits = int(sys.argv[7]) if len(sys.argv) > 7 else None
    A = lambda i: i + 1
    B = lambda i: k + i + 1
    C = lambda i: 2 * k + i + 1          # c_0 .. c_k
    S = lambda i: 3 * k + i + 2
    base = 4 * k + 1
    U = lambda i: base + 3 * i + 1       # u_i = a_i b_i
    V = lambda i: base + 3 * i + 2       # v_i = w_i c_i
    W = lambda i: base + 3 * i + 3       # w_i = a_i ⊕ b_i
    nvars_exp = base + 3 * k
    def eq_and(z, x, y):   # z = x·y
        return [[-z, x], [-z, y], [z, -x, -y]]
    def eq_or(z, x, y):    # z = x+y
        return [[z, -x], [z, -y], [-z, x, y]]
    def eq_xor(z, x, y):   # z = x⊕y
        return [[-z, x, y], [-z, -x, -y], [z, -x, y], [z, x, -y]]
    gates = []
    for i in range(k):
        gates += eq_and(U(i), A(i), B(i)) + eq_and(V(i), W(i), C(i)) + eq_or(C(i + 1), U(i), V(i)) \
               + eq_xor(W(i), A(i), B(i)) + eq_xor(S(i), W(i), C(i))
    units = []
    for i in range(k):
        for val, V in ((a, A), (b, B)):
            if val != "free": units.append([V(i) if (int(val) >> i) & 1 else -V(i)])
            elif maxbits is not None and i >= maxbits: units.append([-V(i)])
    units.append([C(0) if cin else -C(0)])
    if s != "free":
        sv = int(s)
        for i in range(k):
            units.append([S(i) if (sv >> i) & 1 else -S(i)])
        units.append([C(k) if (sv >> k) & 1 else -C(k)])
    def write(path, nv, cls):
        with open(path, "w") as f:
            f.write(f"p cnf {nv} {len(cls)}\n")
            for c in cls: f.write(" ".join(map(str, c)) + " 0\n")
    write(out + ".cnf", nvars_exp, gates + units)
    write(out + ".res.cnf", 4 * k + 1, units)
    inst = [{"table": "full_adder.json", "args": [A(i), B(i), C(i), S(i), C(i + 1)]} for i in range(k)]
    json.dump(inst, open(out + ".boxes.json", "w"), indent=1)
    if a != "free" and b != "free":
        truth = int(a) + int(b) + cin
        print(f"k={k}: a={a} b={b} cin={cin} -> true sum={truth}; asserted s={s} -> expect {'SAT' if s=='free' or int(s)==truth else 'UNSAT'}")
    else:
        print(f"k={k}: a={a} b={b} cin={cin} maxbits={maxbits}; asserted s={s} (search needed)")
    print(f"expanded: {nvars_exp} vars, {len(gates)+len(units)} clauses | residual: {4*k+1} vars, {len(units)} clauses + {k} box instances")

if __name__ == "__main__":
    main()
