# vdescent — rank descent on the variety of exact decompositions (2026-11-14)

A try at a new search method for rank records, made for the question "can we find <3x4x6:53>?".

## The idea

The decompositions of a matrix-multiplication tensor with r products are the zeros of
F(U, V, W) = sum_t U_t (x) V_t (x) W_t - T, a real variety V_r.  Its tangent space at a scheme (the
kernel of the Jacobian of F) always contains two rescalings per product and the orbit of
GL_g1 x GL_g2 x GL_g3.  Whatever it contains beyond those are **moduli**: continuous families of
inequivalent schemes through the point.  A flip graph walks such families at the discrete points a
small ring allows.  Here the walk is continuous and steered: two products can be merged when they
are parallel in two of their three factors, and the potential

    Phi = sum_{s<t} omega_st log(D_st + delta),   D_st = p^U p^V + p^U p^W + p^V p^W,
    p^X_st = 1 - cos^2(angle between X_s and X_t)

falls without bound where a pair becomes mergeable.  A step moves along -grad Phi projected on the
moduli, returns to the variety by Levenberg-Marquardt, and is kept if Phi fell; at a critical point
or a stall it is a random move along the moduli.  Mergeable pairs are merged and the scheme polished
to |F| = 0 at the smaller rank, or the merge is refused.

Two things the first versions got wrong, both instructive.  A plain sparsity penalty on the
products' norms does nothing: the classical algorithm is a local minimum of it, as flip-graph
practice says (a reduction has to be set up first).  And the descent must not use the group orbit:
moving along it changes no scheme but every angle (a GL element that squashes a direction makes all
factors look parallel), and the first runs "descended" by a thousandfold growth of the norms.  A
bound on the norms also keeps out degenerations (a pair that turns parallel as its norms diverge
is border rank, not rank).

## Files

- `../../src/bin/vdescend.rs`: the method (Rust; normal matrix from Gram matrices, kernel projector
  from one Cholesky of N + eps instead of an eigendecomposition, Accelerate's dpotrf; runs in
  parallel).  `vdescend SCHEME --moduli` prints the dimension count alone.
  The same binary has the numerical search from random or warm starts (`--search RANK`,
  `--warm D`: regularized Levenberg-Marquardt), validated through <3x3x4:29> and not beyond, and
  clamping (`--sparse`: a found scheme made sparse, its entries clamped to simple values, verified
  in integers); see `../r346/README.md`.
- `vd.py`: the moduli count in NumPy (the prototype; fine for one scheme at a time).
- `pairs.py`, `descend.py`: the Python prototypes of the descent (`descend.py` is the sparsity
  penalty that does not work).  Too slow beyond toy sizes: use the Rust binary.
- `results_2026-11-14.txt`: the validation and the <3x4x6> runs.

## What it found

Moduli (tangent space minus rescalings and orbit):

| scheme | unknowns | moduli |
|---|---|---|
| classical <2x2x2:8>, <3x3x3:27> | 96, 729 | 18, 144 |
| Strassen, Winograd <2x2x2:7> | 84 | 0 |
| <3x3x6:40> (Smirnov's and DPS's points) | 1800 | 0 |
| <4x4x4:48> (DPS accurate_262) | 2304 | 10 |
| <3x4x6:54>, :56, :57 (Perminov's ternary schemes) | 2916-3078 | 8, 29, 44 |

So the <3x3x6:40> scheme is rigid, and the <3x4x6:54> scheme lies in an 8-parameter family
(first-order count) in which every one of its 54 products moves.

Validation, from the classical algorithm (runs reaching each rank):

| format | known rank | reached |
|---|---|---|
| <2x2x2> | 7 | 7 in 12 of 16 runs (3 s) |
| <2x2x3> | 11 | 11 in 8 of 16 (15 s) |
| <2x3x3> | 15 | 16 in 1 of 8, 17 in 5 |
| <3x3x3> | 23 | 24 in 2 of 8, 25 in 4 |

It finds Strassen's algorithm from the schoolbook one, but stops one short of the record at the
next two sizes: weaker than a flip graph there.

<3x4x6:54>: 5 runs of 400 steps in the 8-parameter family, no pair ever closer than D = 0.02 at
bounded norms, no reduction.  From the rank-57 scheme the descent reaches pairs with D = 0 that do
not merge exactly (norms 30 times the start's): degenerations.  No 53.

By a dimension count this is what to expect near a record: a merge asks 11 or more conditions of a
pair that already shares a factor, the family has 8 parameters.  The method has room where schemes
have many moduli, far from the records, which is where flip graphs already work.
