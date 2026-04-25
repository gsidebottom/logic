# === deps ===
# expr.jq
# math.jq
# at_most.jq
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
def d(i): vi("d";i);

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
def test_faulty_adder:
  faulty_adder(a(0);b(0);c(0);s(0);c(1);u(0);v(0);w(0);d(0,0);d(0,1);d(0,2);d(0,3);d(0,4)) ==
  "(d_0,0' ⇒ (a_0 b_0 = u_0)) (d_0,1' ⇒ (w_0 c_0 = v_0)) (d_0,2' ⇒ (u_0 + v_0 = c_1)) (d_0,3' ⇒ (a_0 ⊕ b_0 = w_0)) (d_0,4' ⇒ (w_0 ⊕ c_0 = s_0))";


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
def test_bit_adder: 
  bit_adder(0) == 
    "((a_0 b_0 = u_0) (w_0 c_0 = v_0) (u_0 + v_0 = c_1) (a_0 ⊕ b_0 = w_0) (w_0 ⊕ c_0 = s_0))";

# faulty adder for bit i
def faulty_bit_adder(i):
    br(
        faulty_adder(
            a(i); b(i);
            c(i);
            s(i);
            c(i+1);
            u(i); v(i); w(i);
            d(i,0); d(i,1); d(i,2); d(i,3); d(i,4)
        )
    )
;

# w wide adder
def adder(w): width(w) | prod(bit_adder(.));
def test_adder:
  br(adder(a(0);b(0);c(0);s(0);c(1);u(0);v(0);w(0))) == bit_adder(0);

# w wide faulty adder adder
def faulty_adder(w): width(w) | prod(faulty_bit_adder(.));
def test_faulty_adder:
  br(
    faulty_adder(
      a(0);b(0);c(0);s(0);c(1);
      u(0);v(0);w(0);
      d(0,0); d(0,1); d(0,2); d(0,3); d(0,4)
    )
  ) == faulty_bit_adder(0);

# diagnoses for 2 wide faulty adder
def diags(w): [range(w) | d(.,0), d(.,1), d(.,2), d(.,3), d(.,4)];

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

# faulty add with adder width w a+b+c_in =? s+c_out
# faulty_add(6;3;19;0;21;0)
# faulty_add(16;371;226;0;empty;empty)
def faulty_add(w;a;b;c_in;s;c_out):
  prod(
    br(prod(v_eq("a";a;w))),
    br(prod(v_eq("b";b;w))),
    lit("c";0;c_in == 1),
    br(prod(v_eq("s";s;w))),
    lit("c";w;c_out == 1),
    faulty_adder(w)
  )
;
def test_faulty_add:
  faulty_add(2;1;1;0;3;0) == 
  "(a_1' a_0) (b_1' b_0) c_0' (s_1 s_0) c_2' ((d_1,0' ⇒ (a_1 b_1 = u_1)) (d_1,1' ⇒ (w_1 c_1 = v_1)) (d_1,2' ⇒ (u_1 + v_1 = c_2)) (d_1,3' ⇒ (a_1 ⊕ b_1 = w_1)) (d_1,4' ⇒ (w_1 ⊕ c_1 = s_1))) ((d_0,0' ⇒ (a_0 b_0 = u_0)) (d_0,1' ⇒ (w_0 c_0 = v_0)) (d_0,2' ⇒ (u_0 + v_0 = c_1)) (d_0,3' ⇒ (a_0 ⊕ b_0 = w_0)) (d_0,4' ⇒ (w_0 ⊕ c_0 = s_0)))";

# diagnoses for 2 wide faulty adder
def diags(w): [range(w) | d(.,0), d(.,1), d(.,2), d(.,3), d(.,4)];
# need to work on a better way
def test_diags: 
  at_most_n(2; diags(1); "x") ==
  "(d_0,0' + x_1,1) (d_0,1' + x_2,1) (d_0,1' + x_1,1' + x_2,2) (x_1,1' + x_2,1) (x_1,2' + x_2,2) (d_0,1' + x_1,2') (d_0,2' + x_3,1) (d_0,2' + x_2,1' + x_3,2) (x_2,1' + x_3,1) (x_2,2' + x_3,2) (d_0,2' + x_2,2') (d_0,3' + x_4,1) (d_0,3' + x_3,1' + x_4,2) (x_3,1' + x_4,1) (x_3,2' + x_4,2) (d_0,3' + x_3,2') (d_0,4' + x_4,2')"
;

# faulty add with adder width w a+b+c_in =? s+c_out at most n faults
# faulty_add_at_most(6;3;19;0;21;0;1)
def faulty_add_at_most(w;a;b;c_in;s;c_out;n):
  prod(
    at_most_n(n; diags(w); "x"),
    faulty_add(w;a;b;c_in;s;c_out)
  )
;
def test_faulty_add_at_most:
  faulty_add_at_most(6;3;19;0;21;0;1) | length == 2525
;

# === tests ===
  test_faulty_adder
, test_bit_adder
, test_adder
, test_faulty_adder
, test_faulty_add
, test_diags
, test_faulty_add_at_most