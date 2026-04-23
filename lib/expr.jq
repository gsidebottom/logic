# variable n_i
def v(n;i): "\(n)_\(i)";

# v sub i where i can be sequence of indexes
def vi(v;i): "\(v)_\([i] | join(","))";

# complement formula .'
def c: "\(.)'";

# positive literal n_i
def p(n;i): v(n;i);

# negative literal n_i'
def n(n;i): v(n;i) | c;

# literal
def lit(n;i;p): if p then p(n;i) else n(n;i) end;

def x: "x";
def x(i): v(x;i);

# brackets around formula f
def br(f): if f == "" then "" else "(\(f))" end;

# or together s
def sum(s):
     [s] | join(" + ")
;

# and together p
def prod(p):
     [p] | join(" ")
;

# = together p
def eq(e):
     [e] | join(" = ")
;

# ⊕ together p
def xor(e):
     [e] | join(" ⊕ ")
;

# ⇒ together p
def imp(i):
     [i] | join(" ⇒ ")
;

# interleave a and b
def interleave(a; b): [[a], [b]] | transpose | flatten[];
# === tests ===
v("x";1) == "x_1", vi("a";1,2) == "a_1,2"