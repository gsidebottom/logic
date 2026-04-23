# === deps ===
# expr.jq
# === end deps ===
def a(i): vi("a";i);
def b(i): vi("b";i);
def c(i): vi("c";i);
def c_in: "c_in";
def c_out: "c_out";
def s(i): vi("s";i);
def u(i): vi("u";i);
def v(i): vi("v";i);
def w(i): vi("w";i);
def d0(i): vi("d0";i);
def d1(i): vi("d1";i);
def d2(i): vi("d2";i);
def d3(i): vi("d3";i);
def d4(i): vi("d4";i);

# adder
def adder(a;b;c_in;s;c_out;u1;u2;u3):
    prod(
        br(eq(prod(a, b), u1)),
        br(eq(prod(u3, c_in), u2)),
        br(eq(sum(u1, u2), c_out)),
        br(eq(xor(a, b), u3)),
        br(eq(xor(u3, c_in), s))
    )
;

# faulty adder
def faulty_adder(a;b;c_in;s;c_out;u1;u2;u3;d0;d1;d2;d3;d4):
    prod(
        br(imp((d0 | c),br(eq(prod(a, b), u1)))),
        br(imp((d1 | c),br(eq(prod(u3, c_in), u2)))),
        br(imp((d2 | c),br(eq(sum(u1, u2), c_out)))),
        br(imp((d3 | c),br(eq(xor(a, b), u3)))),
        br(imp((d4 | c),br(eq(xor(u3, c_in), s))))
    )
;

# adder for bit i
def bit_adder(i):
    br(
        adder(
            a(i); b(i);
            c(i);
            s(i);
            c(i+1);
            u(i); v(i); w(i)
        )
    )
;

# faulty adder for bit i
def faulty_bit_adder(i):
    br(
        faulty_adder(
            a(i); b(i);
            c(i);
            s(i);
            c(i+1);
            u(i); v(i); w(i);
            d0(i); d1(i); d2(i); d3(i); d4(i)
        )
    )
;

# w-1, w-2, .. 0
def width(w): range(w-1;-1;-1);

# w wide adder
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
# add(16;371;226;0;empty;empty)
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

# === tests ===
bit_adder(0) == 
"((a_0 b_0 = u_0) (w_0 c_0 = v_0) (u_0 + v_0 = c_1) (a_0 ⊕ b_0 = w_0) (w_0 ⊕ c_0 = s_0))",

prod(v_eq("x"; 5; 3)) == "x_2 x_1' x_0",

br(adder(a(0);b(0);c(0);s(0);c(1);u(0);v(0);w(0))) == bit_adder(0),

faulty_adder(a(0);b(0);c(0);s(0);c(1);u(0);v(0);w(0);d0(0);d1(0);d2(0);d3(0);d4(0)) ==
"(d0_0' ⇒ (a_0 b_0 = u_0)) (d1_0' ⇒ (w_0 c_0 = v_0)) (d2_0' ⇒ (u_0 + v_0 = c_1)) (d3_0' ⇒ (a_0 ⊕ b_0 = w_0)) (d4_0' ⇒ (w_0 ⊕ c_0 = s_0))",

br(
  faulty_adder(
    a(0);b(0);c(0);s(0);c(1);
    u(0);v(0);w(0);d0(0); 
    d1(0); d2(0); d3(0); d4(0)
  )
) == faulty_bit_adder(0)
