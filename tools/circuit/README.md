# hydra_circuit_satsuma: the circuit stage in front of the fall-through

`sat -b hydra_circuit_satsuma` is `hydra_satsuma` (hydra's Cook, factoring
and XOR stages, satsuma-iter + kissat in Docker as the fall-through) with a
circuit stage between the two, from `logic::circuit`:

1. **Does it apply?**  The gates are read off the clauses and the select
   factoring is tried.  The stage applies when factoring finds at least 64
   products of inputs, put on at least 5% of the gates and shared by at
   least 20 gates each on average: the GenMul multiplier encoding (pairs of
   multiplexers on primary inputs that hide the partial products).  A hash
   or an equivalence miter has products without sharing and is left alone.
   Skipped above 10M clauses.  Cost where it does not apply: 1 to 60 s on
   the biggest instances of the 2026 main track.
2. **The probe.**  CaDiCaL on the original for 20,000 conflicts, with its own
   proof: array multipliers fall in a few hundred conflicts, and the passes
   would cost them seconds to minutes.
3. **The passes.**  `--circuit-passes` (default `factor,cuts`): select
   factoring, then the cut-based writer, each with a DRAT prefix; then the
   vendored CaDiCaL 3.0.1 on what they leave, with the rest of the budget
   and its own proof.

An UNSAT is certified after the verdict: drat-trim on the prefix followed by
the solver's proof, against the formula the stage saw (`drat-trim VERIFIED
UNSAT`, in a budget of its own: `--circuit-verify-secs`).  A SAT model is
extended through the dropped definitions (CaDiCaL), checked against the
formula, and printed over the original variables.  `sat -b hydra_circuit`
is the same stage with hydra's CaDiCaL as the fall-through (no Docker).

    tools/gbd/run_benchmark.py --index <index.jsonl> -b hydra_circuit_satsuma -t 5000 -j 10
    tools/circuit/stage_test.py 0 400        # generated instances, thresholds lowered

Where it fires in the 2026 main track (scan of all 400): the 12
multiplier-verification instances, x-epic_a10-p53_transition and PRP_40_40.
The measurements are in doc/data/certified_preprocessing_2026-09-29.txt.
