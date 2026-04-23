# === deps ===
# expr.jq
# === end deps ===

# waerden's example

def w(j; k; n):
  prod(
    interleave(
        (
          (range(n) + 1) as $d |
          (range(n - ((j-1) * $d)) + 1) as $i |
          br(sum(p("x";$i+(range(j)*$d))))
        )
    ;
        (
          (range(n) + 1) as $d |
          (range(n - ((k-1) * $d)) + 1) as $i |
          br(sum(n("x";$i+(range(k)*$d))))
        )
    )
  )
;
# === tests ===
w(3;3;8) == "(x_1 + x_2 + x_3) (x_1' + x_2' + x_3') (x_2 + x_3 + x_4) (x_2' + x_3' + x_4') (x_3 + x_4 + x_5) (x_3' + x_4' + x_5') (x_4 + x_5 + x_6) (x_4' + x_5' + x_6') (x_5 + x_6 + x_7) (x_5' + x_6' + x_7') (x_6 + x_7 + x_8) (x_6' + x_7' + x_8') (x_1 + x_3 + x_5) (x_1' + x_3' + x_5') (x_2 + x_4 + x_6) (x_2' + x_4' + x_6') (x_3 + x_5 + x_7) (x_3' + x_5' + x_7') (x_4 + x_6 + x_8) (x_4' + x_6' + x_8') (x_1 + x_4 + x_7) (x_1' + x_4' + x_7') (x_2 + x_5 + x_8) (x_2' + x_5' + x_8')"