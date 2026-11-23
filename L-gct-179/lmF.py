import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, itertools, math
from lm2 import P_and_grad, R, C
z = np.exp(2j*np.pi/5)
# Fourier coords: index (i,a) -> matrix e_i (x) w^a, w^a_j = z^(a j)
T = np.zeros((20, 20), complex)
for i in range(4):
    for a in range(5):
        for j in range(5): T[i*5+a, i*5+j] = z**(a*j)
def run(S, seed, iters=2000, N=None, verbose=False, T=T):
    S = np.asarray(S, bool); d = S.shape[0]
    rng = np.random.default_rng(seed)
    neq = sum(math.comb(d + k - 1, k) for k in range(1, R + 1)); N = N or int(1.6*neq)+50
    piv = []
    for k in range(d):
        cand = [f for f in np.flatnonzero(S[k]) if f not in piv]
        piv.append(rng.choice(cand))
    idx = [(k, f) for k in range(d) for f in np.flatnonzero(S[k]) if f not in piv]
    kk = np.array([p[0] for p in idx], int); ff = np.array([p[1] for p in idx], int)
    x = (rng.normal(size=len(idx)) + 1j*rng.normal(size=len(idx)))*0.7
    Cs = (rng.normal(size=(N, d)) + 1j*rng.normal(size=(N, d))) * rng.uniform(0.2, 1.0, size=(N,1))/np.sqrt(d)
    def mkX(x):
        X = np.zeros((d, 20), complex); X[np.arange(d), piv] = 1; X[kk, ff] = x; return X
    def res(x):
        B = mkX(x) @ T; M = 1 + (Cs @ B).reshape(N, R, C)
        p, g = P_and_grad(M); gX = g.reshape(N, -1) @ T.T
        return p - 120, Cs[:, kk] * gX[:, ff]
    r, Jm = res(x); cost = np.vdot(r, r).real; lam = 1e-3
    for it in range(iters):
        H = Jm.conj().T @ Jm; gr = Jm.conj().T @ r; dh = np.diag(H).real
        while True:
            step = np.linalg.solve(H + lam*np.diag(dh + 1e-9), -gr)
            x2 = x + step; r2, J2 = res(x2); c2 = np.vdot(r2, r2).real
            if c2 < cost or lam > 1e12: break
            lam *= 5
        if c2 >= cost: break
        x, r, Jm, cost = x2, r2, J2, c2; lam = max(lam/4, 1e-15)
        if verbose and it % 20 == 0: print(it, cost, flush=True)
        if cost < 1e-26: break
    return cost, mkX(x)
def graded_S(freqs):  # list of frequency per basis vector
    S = np.zeros((len(freqs), 20), bool)
    for k, a in enumerate(freqs): S[k, [i*5+a for i in range(4)]] = True
    return S
if __name__ == '__main__':
    tries = int(sys.argv[1])
    res_all = []
    for comp in itertools.product(range(5), repeat=5):
        if sum(comp) != 7 or max(comp) > 4: continue
        freqs = [a for a in range(5) for _ in range(comp[a])]
        best = 1e9
        for s in range(tries):
            c, X = run(graded_S(freqs), s); best = min(best, c)
            if c < 1e-18: np.save('foundF_%s.npy' % ''.join(map(str, comp)), X); break
        print(comp, 'best %.3e' % best, flush=True)
