import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, itertools
from chk import P
z = np.exp(2j*np.pi/5); I = 1j
V = [np.outer(I**(b*np.arange(4)), z**(a*np.arange(5))) for b in range(4) for a in range(5)]
V = np.array(V)  # (20,4,5), label b*5+a
rng = np.random.default_rng(0)
def ok(S, n=12):
    c = rng.normal(size=(n, len(S))) + 1j*rng.normal(size=(n, len(S)))
    t = np.einsum('nd,dij->nij', c, V[list(S)])
    return np.abs(P(t) - 120).max() < 1e-8
# grow level sets via DFS (level property is hereditary)
good = {1: [ (k,) for k in range(20) if ok((k,)) ]}
for d in range(2, 9):
    good[d] = []
    prev = set(good[d-1])
    for S in good[d-1]:
        for k in range(S[-1]+1, 20):
            T = S + (k,)
            if all(T[:i]+T[i+1:] in prev for i in range(d)) and ok(T): good[d].append(T)
    print(d, len(good[d]), good[d][:5], flush=True)
    if not good[d]: break
