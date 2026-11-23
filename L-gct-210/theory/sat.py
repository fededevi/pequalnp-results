import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ext import *
from t2show import show
def report(name, B, n=5, gb=True, nl=12, showex=False):
    print('=====', name, ': rank', rank(B), 'level', is_level(B, n))
    ex = complement(B, n); print('  tangent extra dirs:', len(ex))
    if showex:
        for e in ex: show(e, n); print()
    if not ex or not gb: return ex, None, None
    conds, cs = ext_conditions(B, ex, n, nl=nl)
    print('  conditions per degree:', {k: len(v) for k, v in sorted(conds.items())})
    G = sp.groebner([q.as_expr() for k in sorted(conds) for q in conds[k]], *cs, modulus=P, order='grevlex')
    print('  GB:', G.exprs if len(str(G.exprs)) < 1500 else str(G.exprs)[:1500] + '...')
    single = [k for k in range(len(ex)) if is_level(B + [ex[k]], n)]
    print('  basis dirs that extend:', single)
    return ex, G, cs
