"""Exact (mod p) toolkit for level spaces of per(J+t), n x n.
p = 2147482921 (= 1 mod 60).
A space is a list of n*n-vectors (row-major) mod p."""
import random, itertools
P = 2147482921  # prime, = 1 mod 60: roots of unity of order 3, 4, 5 exist
def root(k):
    """a primitive k-th root of unity mod P"""
    for g in range(2, 200):
        w = pow(g, (P - 1) // k, P)
        if all(pow(w, d, P) != 1 for d in range(1, k)): return w
W = root(3); W2 = W * W % P; I4 = root(4); Z5 = root(5)

def per(M):
    n = len(M)
    dp = {0: 1}
    for i in range(n):
        nd = {}
        for mask, v in dp.items():
            for j in range(n):
                if not mask >> j & 1:
                    k = mask | 1 << j
                    nd[k] = (nd.get(k, 0) + v * M[i][j]) % P
        dp = nd
    return dp[(1 << n) - 1]

def minor(M, i, j):
    return [[M[a][b] for b in range(len(M)) if b != j] for a in range(len(M)) if a != i]

def grad(M):
    n = len(M)
    return [per(minor(M, i, j)) for i in range(n) for j in range(n)]

def mat(v, n):
    return [[v[i * n + j] % P for j in range(n)] for i in range(n)]

def comb(basis, xs, n):
    v = [0] * (n * n)
    for b, x in zip(basis, xs):
        for k in range(n * n): v[k] = (v[k] + b[k] * x) % P
    return v

def jplus(v, n):
    return [[(1 + v[i * n + j]) % P for j in range(n)] for i in range(n)]

def fact(n):
    r = 1
    for i in range(2, n + 1): r *= i
    return r

def is_level(basis, n, trials=40, rng=random):
    for _ in range(trials):
        xs = [rng.randrange(P) for _ in basis]
        if per(jplus(comb(basis, xs, n), n)) != fact(n) % P: return False
    return True

def rref(rows):
    rows = [r[:] for r in rows]; piv = []; r = 0
    if not rows: return [], []
    m = len(rows[0])
    for c in range(m):
        k = next((i for i in range(r, len(rows)) if rows[i][c] % P), None)
        if k is None: continue
        rows[r], rows[k] = rows[k], rows[r]
        inv = pow(rows[r][c], P - 2, P)
        rows[r] = [x * inv % P for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(x - f * y) % P for x, y in zip(rows[i], rows[r])]
        piv.append(c); r += 1
        if r == len(rows): break
    return rows[:r], piv

def rank(rows): return len(rref(rows)[1])

def nullspace(rows, m):
    R, piv = rref(rows)
    free = [c for c in range(m) if c not in piv]
    out = []
    for f in free:
        v = [0] * m; v[f] = 1
        for r, c in zip(R, piv): v[c] = (-r[f]) % P
        out.append(v)
    return out

def tangent(basis, n, samples=None, rng=random):
    """T(L) = {t : <grad per(J+l), t> = 0 for all l in L}: every level space containing L lies in T(L)."""
    samples = samples or 3 * n * n
    G = [grad(jplus(comb(basis, [rng.randrange(P) for _ in basis], n), n)) for _ in range(samples)]
    return nullspace(G, n * n)

def E(i, j, n, c=1):
    v = [0] * (n * n); v[i * n + j] = c % P; return v
def add(*vs):
    return [sum(x) % P for x in zip(*vs)]
