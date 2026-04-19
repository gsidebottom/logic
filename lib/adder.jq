# v sub i where i can be sequence of indexes
def vi(v;i): "\(v)_\([i] | join(","))";
def a(i): vi("a";i);
def b(i): vi("b";i);
def c(i): vi("c";i);
def u(i): vi("u";i);
def s(i): vi("s";i);

# adder for bit i
def adder(a;b;c_in;s;c_out;u1;u2;u3):
    prod(
        br(eq(prod(a, b), u1)),
        br(eq(prod(u3, c_in), u2)),
        br(eq(sum(u1, u2), c_out)),
        br(eq(xor(a, b), u3)),
        br(eq(xor(u3, c_in), s))
    )
;

# adder for bit i
def bit_adder(i):
    adder(
        vi("a";i);
        vi("b";i);
        vi("c";i);
        vi("s";i);
        vi("c";i+1);
        vi("u";i,1);
        vi("u";i,2);
        vi("u";i,3)
    )
;

# prod(a(0), b(0), c(0), a(1), b(1), c(1), bit_adder(0), bit_adder(1))
