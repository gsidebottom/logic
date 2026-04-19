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

#
def width(w): range(w-1;-1;-1);

def adder(w): width(w) | prod(bit_adder(.));

# call [bit_position;bit_value] | f for each bit in . as a number w wide.  bit_value is true or false
def bits(w; f):
  . as $n |
  width(w) |
  [., (($n / pow(2; .)) | floor) % 2 == 1] | f
;

# name_(w-1)^(w-1)+...+name_0 = num
def v_eq(name;num;w):
    num |
    bits(w;lit(name;.[0];.[1]))
;

# add with adder width w a+b+c_in = s+c_out
# can use empty for unconstrained for example 6 bit adder 3+19+0 = ?+?
# add(6;3;19;0;empty;empty)
def add(w;a;b;c_in;s;c_out):
  prod(
    br(prod(v_eq("a";a;w))),
    br(prod(v_eq("b";b;w))),
    lit("c";0;c_in == 1),
    br(prod(v_eq("s";s;w))),
    lit("c";w;c_out == 1),
    adder(w)
  )
;

