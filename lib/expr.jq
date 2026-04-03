# variable n_i
def v(n;i): "\(n)_\(i)";

# complement formula .'
def c: "\(.)'";

# positive literal n_i
def p(n;i): v(n;i);

# negative literal n_i'
def n(n;i): v(n;i) | c;

def x: "x";
def x(i): v(x;i);

# brackets around formula (.)
def b(f): "(\(f))";

# or together s
def sum(s):
     [s] | join(" + ")
;

# and together p
def prod(p):
     [p] | join(" ")
;