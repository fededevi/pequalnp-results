import numpy as np, itertools, sys, math, os
R, C = 4, 5
INJ = np.array([p for p in itertools.permutations(range(C), R)])   # (120,4)
def P_and_grad(M):
    N = M.shape[0]
    E = M[:, np.arange(R)[None, :], INJ]   # (N,120,4)
    P = E.prod(axis=2).sum(axis=1)
    g = np.zeros_like(M)
    for i in range(R):
        oth = np.delete(E, i, axis=2).prod(axis=2)
        for j in range(C):
            g[:, i, j] = oth[:, INJ[:, i] == j].sum(axis=1)
    return P, g
def run(d, seed, iters=400, mask=None, N=None, verbose=False, B0=None):
    rng = np.random.default_rng(seed)
    neq = sum(math.comb(d + k - 1, k) for k in range(1, R + 1))
    N = N or int(1.6 * neq) + 50
    B = (rng.normal(size=(d, R, C)) + 1j * rng.normal(size=(d, R, C))) * 0.5
    if B0 is not None: B = B0.copy()
    Cs = (rng.normal(size=(N, d)) + 1j * rng.normal(size=(N, d)))
    Cs *= rng.uniform(0.3, 1.5, size=(N, 1)) / np.sqrt(d)
    if mask is None: mask = np.ones((R, C))
    mi = np.flatnonzero(np.tile(mask.reshape(-1), d)); B = B * mask
    def orth(B):
        Q, _ = np.linalg.qr(B.reshape(d, -1).T); return Q.T.reshape(d, R, C)
    def res(B):
        M = 1 + np.einsum('md,dij->mij', Cs, B)
        p, g = P_and_grad(M); return p - 120, g
    B = orth(B); r, g = res(B); cost = np.vdot(r, r).real; lam = 1e-2
    for it in range(iters):
        Jm = np.einsum('md,mij->mdij', Cs, g).reshape(N, -1)[:, mi]
        H = Jm.conj().T @ Jm; gr = Jm.conj().T @ r
        dm = np.diag(H).real.mean()
        while True:
            step = np.linalg.solve(H + lam * (1 + dm) * np.eye(H.shape[0]), -gr)
            B2 = B.copy().reshape(-1); B2[mi] += step; B2 = orth(B2.reshape(d, R, C))
            r2, g2 = res(B2); c2 = np.vdot(r2, r2).real
            if c2 < cost or lam > 1e10: break
            lam *= 4
        if c2 < cost:
            B, r, g, cost = B2, r2, g2, c2; lam = max(lam / 3, 1e-14)
        else: break
        if verbose and it % 20 == 0: print(it, cost, lam, flush=True)
        if cost < 1e-24: break
    return cost, B
if __name__ == '__main__':
    d = int(sys.argv[1]); s0, s1 = int(sys.argv[2]), int(sys.argv[3])
    for s in range(s0, s1):
        cost, B = run(d, s)
        print(d, s, 'cost %.3e' % cost, flush=True)
        if cost < 1e-18: np.save(f'found_d{d}_s{s}.npy', B)
