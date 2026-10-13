# Verbatim from Stapleton & Perminov, arXiv:2609.32388 (Sept 26, 2026),
# paper listing "Python script for verification of the 51-addition alt.
# basis scheme"; cached arXiv source scratchpad sp51/main.tex, extracted
# 2026-10-13.  Their certificate (cert.json here) accompanies the paper.
# Stored unmodified as the verification target for proof/Mm/SP51.lean
# (see matmul/gen_sp51_lean.py).
import json
import numpy as np


def multiply3x3_cr51(a: np.ndarray, b: np.ndarray) -> np.ndarray:
    a0, a1, a2, a3, a4, a5, a6, a7, a8 = a.reshape(9)
    b0, b1, b2, b3, b4, b5, b6, b7, b8 = b.reshape(9)

    x0, x1, x2 = a0, a1, a2
    x3, x4, x5 = a3, a4, a5
    x6, x7, x8 = a6, a7, a8 - a6

    y0, y1, y2 = b0, b1, b2 + b0
    y3, y4, y5 = b3, b4, b5
    y6, y7, y8 = b6 - b7, b7, b8 + b5

    # 13 additions
    u0 = x0
    u1 = x1
    u2 = x1
    u3 = x3
    u4 = x4
    u5 = x4
    u6 = x5
    u7 = x6
    u8 = x7
    u9 = x7
    u10 = x8
    u11 = x5 + x8
    u12 = x1 - x2
    u13 = x8 + u12
    u14 = x6 + u13
    u15 = x3 - u11
    u16 = x7 - u14
    u17 = x6 + u11
    u18 = x4 - x5
    u22 = x0 - u15
    u19 = x2 - u22
    u20 = x5 + u19
    u21 = x3 - u20
    u22 = u17 - u22

    # 12 additions
    v0 = y2
    v11 = y0 + y6
    v7 = y1 - v11
    v13 = y2 + v7
    v21 = y6 + v13
    v20 = y8 + v21
    v14 = y7 + v20
    v2 = y4 + v14
    v17 = y7 + v11
    v22 = y1 - v20
    v12 = v13 - v14
    v1 = y3 - v12
    v12 = y5 + v12
    v3 = y1
    v4 = y3
    v5 = y4
    v6 = y7
    v8 = y3
    v9 = y4
    v10 = y6
    v15 = y0
    v16 = y5
    v18 = y5
    v19 = y8

    p0 = u0 * v0
    p1 = u1 * v1
    p2 = u2 * v2
    p3 = u3 * v3
    p4 = u4 * v4
    p5 = u5 * v5
    p6 = u6 * v6
    p7 = u7 * v7
    p8 = u8 * v8
    p9 = u9 * v9
    p10 = u10 * v10
    p11 = u11 * v11
    p12 = u12 * v12
    p13 = u13 * v13
    p14 = u14 * v14
    p15 = u15 * v15
    p16 = u16 * v16
    p17 = u17 * v17
    p18 = u18 * v18
    p19 = u19 * v19
    p20 = u20 * v20
    p21 = u21 * v21
    p22 = u22 * v22

    # 26 additions
    t0 = p11 - p10 + p6
    t1 = p20 + p21 - p3
    t2 = p22 + t1
    t3 = p17 - t0
    t4 = p7 + t3
    t5 = t4 - p14 - t2
    t6 = p13 + t5

    z0 = p0 + p1 + t6
    z1 = p2 - p10 + p21 + t5
    z2 = p12 - t6
    z3 = p4 + p15 + t0
    z4 = p5 + p6 + p3
    z5 = p18 - p19 + t1
    z6 = p8 + t3
    z7 = p9 - p10 + t4
    z8 = p16 - t2

    c = np.array([z0, z1, z2, z3, z4, z5, z6, z7, z8 + z2])
    return c.reshape(3, 3)


def main():
    with open("3x3x3_m23_cr51_alt_basis_certificate.json", "r") as f:
        data = json.load(f)

    U = np.array(data["original_matrices"]["U"])
    V = np.array(data["original_matrices"]["V"])
    W = np.array(data["original_matrices"]["W"])

    Uc = np.array(data["changed_matrices"]["U"])
    Vc = np.array(data["changed_matrices"]["V"])
    Wc = np.array(data["changed_matrices"]["W"])

    P = np.array(data["basis"]["P"])
    Q = np.array(data["basis"]["Q"])
    R = np.array(data["basis"]["R"])

    # check valid basis conversion
    assert np.allclose(U, Uc @ P)
    assert np.allclose(V, Vc @ Q)
    assert np.allclose(W, R @ Wc)

    # check Brent equations
    tensor = np.zeros((9, 9, 9), dtype=np.int32)
    for i in range(3):
        for j in range(3):
            for k in range(3):
                tensor[i * 3 + k, k * 3 + j, i * 3 + j] = 1

    assert np.allclose(tensor, np.einsum("ri,rj,kr->ijk", U, V, W))

    for _ in range(1000):
        a, b = np.random.randn(3, 3), np.random.randn(3, 3)
        c = a @ b

        x = P @ a.reshape(9)
        y = Q @ b.reshape(9)

        u = Uc @ x
        v = Vc @ y
        p = u * v
        z = Wc @ p

        # check the full scheme in the new basis
        assert np.allclose(c, (R @ z).reshape(3, 3))
        # check the reduced scheme in the new basis
        assert np.allclose(c, multiply3x3_cr51(a, b))

    print("All tests passed")


if __name__ == '__main__':
    main()
