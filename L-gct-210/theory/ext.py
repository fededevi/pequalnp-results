import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lvl import *
import sympy as sp
from itertools import combinations_with_replacement as cwr

def complement(B, n):
    T = tangent(B, n); out = []; cur = B[:]
    for t in T:
        if rank(cur + [t]) > rank(cur): out.append(t); cur.append(t)
    return out

def per_poly(M, n, gens):
    """M entries: sympy Poly over GF(P)."""
    one = sp.Poly(1, *gens, modulus=P)
    dp = {0: one}
    for i in range(n):
        nd = {}
        for mask, v in dp.items():
            for j in range(n):
                if not mask >> j & 1:
                    k = mask | 1 << j
                    nd[k] = nd[k] + v * M[i][j] if k in nd else v * M[i][j]
        dp = nd
    return dp[(1 << n) - 1]

def ext_conditions(B, ex, n, nl=12, rng=random):
    """Polynomials in c (one var per vector of ex) that must vanish for L + C*sum c_i ex_i to be level.
    Returns dict degree -> list of sympy Polys (a basis of the sampled condition space, mod P)."""
    m = len(ex); cs = sp.symbols(f'c0:{m}'); s = sp.Symbol('s'); gens = (s,) + cs
    res = {}
    for _ in range(nl):
        l = comb(B, [rng.randrange(P) for _ in B], n)
        M = [[sp.Poly(1 + l[i*n+j] + s*sum(int(ex[k][i*n+j])*cs[k] for k in range(m)), *gens, modulus=P)
              for j in range(n)] for i in range(n)]
        pp = per_poly(M, n, gens)
        for mon, co in pp.terms():
            if mon[0] >= 2:
                res.setdefault(mon[0], []).append((mon[1:], co, _))
    out = {}
    for k, items in res.items():
        mons = sorted({mo for mo, _, _ in items})
        idx = {mo: i for i, mo in enumerate(mons)}
        rows = {}
        for mo, co, smp in items:
            rows.setdefault(smp, [0]*len(mons))[idx[mo]] = int(co) % P
        R, piv = rref(list(rows.values()))
        out[k] = [sp.Poly(sum(int(r[i]) * sp.prod([c**e for c, e in zip(cs, mons[i])]) for i in range(len(mons))), *cs, modulus=P) for r in R]
    return out, cs
