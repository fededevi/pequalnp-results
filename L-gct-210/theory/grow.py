import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ext import *
from t2show import show

def roots_mod(f, x):
    pf = sp.Poly(f, x, modulus=P)
    if pf.is_zero: return None
    out = []
    for fac, _ in pf.factor_list()[1]:
        if fac.degree() == 1:
            a, b = fac.all_coeffs(); out.append((-b * pow(int(a), P - 2, P)) % P)
    return out

def solve_zero_dim(polys, ys):
    """rational points mod P of a (hopefully zero-dimensional) system, by lex Groebner + back substitution"""
    if not ys:
        return [[]] if all(sp.Poly(q, modulus=P).is_zero if q != 0 else True for q in polys) else []
    G = sp.groebner(polys, *ys, modulus=P, order='lex').exprs
    if G == [1]: return []
    last = ys[-1]
    uni = [g for g in G if g.free_symbols <= {last}]
    if not uni: return None          # positive dimensional slice
    rts = roots_mod(uni[0], last)
    sols = []
    for r in rts:
        sub = [sp.Poly(g.subs(last, r), *ys[:-1], modulus=P).as_expr() if len(ys) > 1 else g.subs(last, r) for g in G]
        if len(ys) == 1:
            if all(int(v) % P == 0 for v in sub): sols.append([r])
            continue
        sub = [g for g in sub if g != 0]
        rest = solve_zero_dim(sub, ys[:-1]) if sub else None
        if rest is None: return None
        sols += [s + [r] for s in rest]
    return sols

def ext_points(B, n, rng=random, nl=12, verbose=True):
    """Find extension directions t (mod L) with L + C t level; returns (ex, list of t-vectors, slice dim)."""
    ex = complement(B, n); m = len(ex)
    if m == 0: return ex, [], None
    if m == 1:
        return ex, ([ex[0]] if is_level(B + ex, n) else []), 0
    conds, cs = ext_conditions(B, ex, n, nl=nl, rng=rng)
    polys = [q.as_expr() for k in sorted(conds) for q in conds[k]]
    for d in range(0, m):
        ys = sp.symbols(f'y0:{d}') if d else ()
        base = [rng.randrange(P) for _ in range(m)]
        dirs = [[rng.randrange(P) for _ in range(m)] for _ in range(d)]
        sub = {cs[i]: base[i] + sum(dirs[k][i] * ys[k] for k in range(d)) for i in range(m)}
        sl = [sp.Poly(q.subs(sub), *ys, modulus=P).as_expr() if d else int(q.subs(sub)) % P for q in polys]
        sl = [q for q in sl if q != 0]
        if d == 0:
            if not sl: return ex, [comb(ex, base, n)], 0
            continue
        sols = solve_zero_dim(sl, list(ys))
        if sols is None:
            if verbose: print('   slice dim', d, 'positive dimensional?'); continue
        if sols:
            pts = []
            for s in sols:
                c = [(base[i] + sum(dirs[k][i] * s[k] for k in range(d))) % P for i in range(m)]
                t = comb(ex, c, n)
                if is_level(B + [t], n): pts.append(t)
            if pts: return ex, pts, d
        elif sp.groebner(sl, *ys, modulus=P).exprs != [1]:
            if verbose: print('   slice dim', d, ': points exist but none rational mod P')
    return ex, [], None

def grow(name, B, n=5, rng=random):
    B = B[:]
    print('=====', name, 'start dim', rank(B), 'level', is_level(B, n))
    while True:
        ex, pts, d = ext_points(B, n, rng=rng)
        print('   dim', rank(B), ': tangent extras', len(ex), '; extension variety: codim-slice', d, ', rational pts found', len(pts))
        if not pts: break
        B.append(pts[0])
    print('   MAXIMAL (within what was found): dim', rank(B)); return B
if __name__ == '__main__':
    random.seed(11); n = 5
    def exo(rows, cols):
        a, b, c, d = cols; r0, r1, r2 = rows
        b1 = add(E(r0,a,n),E(r0,b,n,-1),E(r1,a,n,W),E(r1,b,n,-W),E(r2,a,n,W2),E(r2,b,n,-W2))
        b2 = add(E(r0,c,n),E(r0,d,n,-1),E(r1,c,n,W2),E(r1,d,n,-W2),E(r2,c,n,W),E(r2,d,n,-W))
        return [b1, b2]
    X = exo((0,1,2),(0,1,2,3))
    for j in range(4): X.append(add(E(3,j,n),E(3,4,n,-1)))
    grow('exotic6', X)
    grow('exotic2', exo((0,1,2),(0,1,2,3)))
