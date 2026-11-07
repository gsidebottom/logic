#!/usr/bin/env python3
"""Projections of an F2 matrix-multiplication scheme to a smaller format by
the substitution method (Pan 1966; the lemma on
fmm.univ-lille.fr/projalongmode.html, which Sedoglavic used on 2026-11-04/06
to lower 62 catalog entries):

  col      <n1,n2,n3:r> -> <n1,n2,n3-1 : r-n2>   kill a column direction of B and C
  row      <n1,n2,n3:r> -> <n1-1,n2,n3 : r-n2>   kill a row direction of A and C
  inner-a  <n1,n2,n3:r> -> <n1,n2-1,n3 : r-n1>   kill an inner direction, substituting A's column
  inner-b  <n1,n2,n3:r> -> <n1,n2-1,n3 : r-n3>   kill an inner direction, substituting B's row

Killing a direction d: apply the format symmetry that makes d the last
index (A -> hA, C -> hC for a row; B -> Bg, C -> Cg for a column; A -> Ag,
B -> g^-1 B for the inner index), take the q killed variables (the last
column of B, the last row of A, ...), pick q products whose forms
restricted to those variables are independent, substitute the killed
variables by the linear forms that make those q products vanish, and drop
the killed outputs.  The remaining r - q products compute the smaller
product.  Over F2 every nonzero direction (2^n - 1 of them) and every
basis among the restricted forms gives a projection; this tool takes all
directions and all or sampled bases, checks every output against the
matmul tensor, dedupes by sorted terms, and writes .bits files in the
repository's layout (all a factors, then b, then c; a bit i*n2+k, b bit
k*n3+j, c bit i*n3+j).

usage: project_f2.py N1 N2 N3 in.bits --mode col|row|inner-a|inner-b --out DIR
       [--per-dir 20] [--enum-limit 20000] [--seed 1] [--max 2000] [--quiet]
"""
import argparse, itertools, os, random, sys
import numpy as np


def rank_f2(M):
    M = (np.array(M, dtype=np.uint8) % 2).copy()
    r = 0
    rows, cols = M.shape
    for c in range(cols):
        piv = None
        for i in range(r, rows):
            if M[i, c]:
                piv = i
                break
        if piv is None:
            continue
        M[[r, piv]] = M[[piv, r]]
        for i in range(rows):
            if i != r and M[i, c]:
                M[i] ^= M[r]
        r += 1
        if r == rows:
            break
    return r


def inv_f2(M):
    n = M.shape[0]
    A = np.concatenate([np.array(M, dtype=np.uint8) % 2, np.eye(n, dtype=np.uint8)], axis=1)
    r = 0
    for c in range(n):
        piv = None
        for i in range(r, n):
            if A[i, c]:
                piv = i
                break
        if piv is None:
            raise ValueError("singular")
        A[[r, piv]] = A[[piv, r]]
        for i in range(n):
            if i != r and A[i, c]:
                A[i] ^= A[r]
        r += 1
    return A[:, n:]


def basis_with_last(d, n, as_row):
    """an invertible n x n matrix over F2 whose last column (or row) is d"""
    piv = int(np.flatnonzero(d)[0])
    others = [j for j in range(n) if j != piv]
    cols = [np.eye(n, dtype=np.uint8)[j] for j in others] + [np.array(d, dtype=np.uint8)]
    g = np.stack(cols, axis=1)  # columns
    return g.T.copy() if as_row else g


def expected_tensor(n1, n2, n3):
    E = np.zeros((n1 * n2, n2 * n3, n1 * n3), dtype=np.uint8)
    for i in range(n1):
        for k in range(n2):
            for j in range(n3):
                E[i * n2 + k, k * n3 + j, i * n3 + j] = 1
    return E


def check(alpha, beta, gamma, n1, n2, n3):
    A = alpha.reshape(alpha.shape[0], -1)
    B = beta.reshape(beta.shape[0], -1)
    C = gamma.reshape(gamma.shape[0], -1)
    T = np.einsum('sa,sb,sc->abc', A, B, C) % 2
    return np.array_equal(T, expected_tensor(n1, n2, n3))


def load_bits(path, n1, n2, n3):
    txt = open(path).read().split()[-1]
    bits = np.array([int(ch) for ch in txt], dtype=np.uint8)
    w = n1 * n2 + n2 * n3 + n1 * n3
    assert bits.size % w == 0, (bits.size, w)
    r = bits.size // w
    sa, sb = r * n1 * n2, r * n2 * n3
    alpha = bits[:sa].reshape(r, n1, n2)
    beta = bits[sa:sa + sb].reshape(r, n2, n3)
    gamma = bits[sa + sb:].reshape(r, n1, n3)
    return alpha, beta, gamma


def to_bits(alpha, beta, gamma):
    return ''.join(str(int(x)) for x in np.concatenate([alpha.reshape(-1), beta.reshape(-1), gamma.reshape(-1)]))


def term_key(alpha, beta, gamma):
    r = alpha.shape[0]
    terms = []
    for s in range(r):
        terms.append((alpha[s].tobytes(), beta[s].tobytes(), gamma[s].tobytes()))
    return tuple(sorted(terms))


def substitute(forms_killed, forms_rest, E):
    """forms_killed: (r, q), forms_rest: (r, m). Returns the (r-q, m) rest
    forms after substituting the killed variables so the products E vanish."""
    F = forms_killed[E]            # q x q, invertible
    G = forms_rest[E]              # q x m
    L = (inv_f2(F) @ G) % 2        # q x m: killed = L @ rest
    keep = [s for s in range(forms_killed.shape[0]) if s not in set(E)]
    new = (forms_rest[keep] + forms_killed[keep] @ L) % 2
    return keep, new.astype(np.uint8)


def bases(forms, q, rng, per_dir, enum_limit):
    """index sets E of size q with independent restricted forms: all of
    them when few enough, else per_dir random ones"""
    r = forms.shape[0]
    cand = [s for s in range(r) if forms[s].any()]
    total = 1
    for i in range(q):
        total = total * (len(cand) - i) // (i + 1)
    out = []
    if total <= enum_limit:
        for E in itertools.combinations(cand, q):
            if rank_f2(forms[list(E)]) == q:
                out.append(list(E))
    else:
        seen = set()
        tries = 0
        while len(out) < per_dir and tries < per_dir * 50:
            tries += 1
            E = tuple(sorted(rng.sample(cand, q)))
            if E in seen:
                continue
            seen.add(E)
            if rank_f2(forms[list(E)]) == q:
                out.append(list(E))
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('n1', type=int); ap.add_argument('n2', type=int); ap.add_argument('n3', type=int)
    ap.add_argument('bits')
    ap.add_argument('--mode', required=True, choices=['col', 'row', 'inner-a', 'inner-b'])
    ap.add_argument('--out', required=True)
    ap.add_argument('--per-dir', type=int, default=20)
    ap.add_argument('--enum-limit', type=int, default=20000)
    ap.add_argument('--seed', type=int, default=1)
    ap.add_argument('--max', type=int, default=2000)
    ap.add_argument('--quiet', action='store_true')
    a = ap.parse_args()
    n1, n2, n3 = a.n1, a.n2, a.n3
    alpha, beta, gamma = load_bits(a.bits, n1, n2, n3)
    r = alpha.shape[0]
    assert check(alpha, beta, gamma, n1, n2, n3), "input fails the tensor check"
    rng = random.Random(a.seed)
    os.makedirs(a.out, exist_ok=True)
    seen = set()
    written = 0
    tried = 0
    failed = 0
    if a.mode == 'col':
        ndir, q, m1, m2, m3 = n3, n2, n1, n2, n3 - 1
    elif a.mode == 'row':
        ndir, q, m1, m2, m3 = n1, n2, n1 - 1, n2, n3
    elif a.mode == 'inner-a':
        ndir, q, m1, m2, m3 = n2, n1, n1, n2 - 1, n3
    else:
        ndir, q, m1, m2, m3 = n2, n3, n1, n2 - 1, n3
    for dcode in range(1, 1 << ndir):
        d = np.array([(dcode >> i) & 1 for i in range(ndir)], dtype=np.uint8)
        if a.mode == 'col':
            g = basis_with_last(d, n3, as_row=False)
            ginv = inv_f2(g)
            beta2 = (beta @ ginv.T) % 2
            gamma2 = (gamma @ g) % 2
            killed = beta2[:, :, n3 - 1]                       # (r, n2)
            rest = beta2[:, :, :n3 - 1].reshape(r, -1)         # (r, n2 (n3-1))
            for E in bases(killed, q, rng, a.per_dir, a.enum_limit):
                keep, new = substitute(killed, rest, E)
                al = alpha[keep]
                be = new.reshape(len(keep), n2, n3 - 1)
                ga = gamma2[keep][:, :, :n3 - 1]
                yield_one = (al, be, ga)
                tried += 1
                if not check(*yield_one, m1, m2, m3):
                    failed += 1
                    continue
                key = term_key(*yield_one)
                if key in seen:
                    continue
                seen.add(key)
                open(f'{a.out}/proj{m1}{m2}{m3}_{len(keep)}_{written:05d}.bits', 'w').write(to_bits(*yield_one) + '\n')
                written += 1
                if written >= a.max:
                    break
        elif a.mode == 'row':
            h = basis_with_last(d, n1, as_row=True)
            hinv = inv_f2(h)
            alpha2 = np.einsum('li,sik->slk', hinv.T % 2, alpha) % 2
            gamma2 = np.einsum('li,sij->slj', h, gamma) % 2
            killed = alpha2[:, n1 - 1, :]                      # (r, n2)
            rest = alpha2[:, :n1 - 1, :].reshape(r, -1)
            for E in bases(killed, q, rng, a.per_dir, a.enum_limit):
                keep, new = substitute(killed, rest, E)
                al = new.reshape(len(keep), n1 - 1, n2)
                be = beta[keep]
                ga = gamma2[keep][:, :n1 - 1, :]
                tried += 1
                if not check(al, be, ga, m1, m2, m3):
                    failed += 1
                    continue
                key = term_key(al, be, ga)
                if key in seen:
                    continue
                seen.add(key)
                open(f'{a.out}/proj{m1}{m2}{m3}_{len(keep)}_{written:05d}.bits', 'w').write(to_bits(al, be, ga) + '\n')
                written += 1
                if written >= a.max:
                    break
        else:
            g = basis_with_last(d, n2, as_row=False)
            ginv = inv_f2(g)
            alpha2 = (alpha @ ginv.T) % 2                      # A' = A g
            beta2 = np.einsum('kl,skj->slj', g, beta) % 2      # B' = g^-1 B  =>  beta' = g^T beta
            if a.mode == 'inner-a':
                killed = alpha2[:, :, n2 - 1]                  # (r, n1)
                rest = alpha2[:, :, :n2 - 1].reshape(r, -1)
            else:
                killed = beta2[:, n2 - 1, :]                   # (r, n3)
                rest = beta2[:, :n2 - 1, :].reshape(r, -1)
            for E in bases(killed, q, rng, a.per_dir, a.enum_limit):
                keep, new = substitute(killed, rest, E)
                if a.mode == 'inner-a':
                    al = new.reshape(len(keep), n1, n2 - 1)
                    be = beta2[keep][:, :n2 - 1, :]
                else:
                    al = alpha2[keep][:, :, :n2 - 1]
                    be = new.reshape(len(keep), n2 - 1, n3)
                ga = gamma[keep]
                tried += 1
                if not check(al, be, ga, m1, m2, m3):
                    failed += 1
                    continue
                key = term_key(al, be, ga)
                if key in seen:
                    continue
                seen.add(key)
                open(f'{a.out}/proj{m1}{m2}{m3}_{len(keep)}_{written:05d}.bits', 'w').write(to_bits(al, be, ga) + '\n')
                written += 1
                if written >= a.max:
                    break
        if written >= a.max:
            break
    print(f'{a.mode}: <{n1},{n2},{n3}:{r}> -> <{m1},{m2},{m3}:{r - q}>; directions {ndir and (1 << ndir) - 1}, '
          f'projections tried {tried}, failed check {failed}, distinct written {written} -> {a.out}')


if __name__ == '__main__':
    main()
