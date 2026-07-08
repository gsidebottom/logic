import Mm55proof.Rigid48
open Rigid48
def main : IO Unit := do
  let r := explore seed 20000
  IO.println s!"visited={r.visited} saturated={r.saturated} allValid={r.allValid} noBad={r.noBadReduction}"
