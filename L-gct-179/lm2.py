import numpy as np, itertools, sys, math
R, C = 4, 5
INJ = np.array([p for p in itertools.permutations(range(C), R)])
def P_and_grad(M):
    E = M[:, np.arange(R)[None, :], INJ]
    P = E.prod(axis=2).sum(axis=1)
    g = np.zeros_like(M)
    for i in range(R):
        oth = np.delete(E, i, axis=2).prod(axis=2)
        for j in range(C):
            g[:, i, j] = oth[:, INJ[:, i] == j].sum(axis=1)
    return P, g
def run(d, seed, iters=1500, mask=None, N=None, verbose=False, piv=None, X0=None):
    rng = np.random.default_rng(seed)
    neq = sum(math.comb(d + k - 1, k) for k in range(1, R + 1))
    N = N or int(1.6 * neq) + 50
    if mask is None: mask = np.ones(R*C)
    mask = np.asarray(mask).reshape(-1)
    allowed = np.flatnonzero(mask)
    if piv is None: piv = rng.choice(allowed, d, replace=False)
    free = np.array([k for k in allowed if k not in set(piv)])
    X = (rng.normal(size=(d, len(free))) + 1j*rng.normal(size=(d, len(free))))*0.7 if X0 is None else X0
    Cs = (rng.normal(size=(N, d)) + 1j*rng.normal(size=(N, d))) * rng.uniform(0.2, 1.0, size=(N,1))/np.sqrt(d)
    def mkB(X):
        B = np.zeros((d, R*C), complex); B[np.arange(d), piv] = 1; B[:, free] = X; return B
    def res(X):
        B = mkB(X); M = 1 + (Cs @ B).reshape(N, R, C)
        p, g = P_and_grad(M); return p - 120, g.reshape(N, -1)[:, free]
    r, g = res(X); cost = np.vdot(r, r).real; lam = 1e-3
    for it in range(iters):
        Jm = (Cs[:, :, None] * g[:, None, :]).reshape(N, -1)
        H = Jm.conj().T @ Jm; gr = Jm.conj().T @ r; dh = np.diag(H).real
        while True:
            step = np.linalg.solve(H + lam*np.diag(dh + 1e-9), -gr)
            X2 = X + step.reshape(X.shape); r2, g2 = res(X2); c2 = np.vdot(r2, r2).real
            if c2 < cost or lam > 1e12: break
            lam *= 5
        if c2 >= cost: break
        X, r, g, cost = X2, r2, g2, c2; lam = max(lam/4, 1e-15)
        if verbose and it % 20 == 0: print(it, cost, lam, np.abs(X).max(), flush=True)
        if cost < 1e-26: break
    return cost, mkB(X), piv, X
if __name__ == '__main__':
    d = int(sys.argv[1]); s0, s1 = int(sys.argv[2]), int(sys.argv[3])
    for s in range(s0, s1):
        cost, B, piv, X = run(d, s)
        print(d, s, 'cost %.3e' % cost, 'max|X| %.2e' % np.abs(X).max(), flush=True)
        if cost < 1e-18: np.save(f'found2_d{d}_s{s}.npy', B)
