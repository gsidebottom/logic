
# waerden's example

def w(j; k; n):
  prod(
    interleave(
        (
          (range(n) + 1) as $d |
          (range(n - ((j-1) * $d)) + 1) as $i |
          b(sum(p("x";$i+(range(j)*$d))))
        )
    ;
        (
          (range(n) + 1) as $d |
          (range(n - ((k-1) * $d)) + 1) as $i |
          b(sum(n("x";$i+(range(k)*$d))))
        )
    )
  )
;