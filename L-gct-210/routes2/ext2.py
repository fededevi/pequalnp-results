"""Extend a fixed level space D (k,n,n) by e free vectors inside its first-order extension space."""
import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm, math
def grad_span(D, N=300, seed=5):
    k, n, _ = D.shape; perms = lm.setup(n); rng = np.random.default_rng(seed)
    C = rng.normal(size=(N, k)) + 1j * rng.normal(size=(N, k))
    _, g = lm.per_and_grad(1 + np.einsum('md,dij->mij', C, D), perms)
    return g.reshape(N, n * n)
def ext_space(D):
    k, n, _ = D.shape
    G = grad_span(D)
    # t in ext space iff sum G_m . t = 0 (bilinear) ; and orthogonal (hermitian) to D
    M = np.vstack([G, D.reshape(k, -1).conj()])
    u, s, vh = np.linalg.svd(M); r = int((s > 1e-8 * s[0]).sum())
    return vh[r:].conj()            # rows: basis of {t: M t = 0}
def extend(D, e, seed, iters=300, Nb=None):
    k, n, _ = D.shape; d = k + e; perms = lm.setup(n); rng = np.random.default_rng(seed)
    if Nb is None: Nb = ext_space(D)
    q = len(Nb)
    neq = sum(math.comb(d + j - 1, j) for j in range(1, n + 1)); N = int(1.3 * neq) + 50
    C = (rng.normal(size=(N, d)) + 1j * rng.normal(size=(N, d))) * rng.uniform(0.3, 1.5, size=(N, 1)) / np.sqrt(d)
    f = math.factorial(n)
    def orth(Y):
        Q, _ = np.linalg.qr(Y.T); return Q.T
    def res(Y):
        B = np.concatenate([D, (Y @ Nb).reshape(e, n, n)])
        p, g = lm.per_and_grad(1 + np.einsum('md,dij->mij', C, B), perms); return p - f, g
    Y = orth(rng.normal(size=(e, q)) + 1j * rng.normal(size=(e, q)))
    r, g = res(Y); cost = np.vdot(r, r).real; lam = 1e-2
    for it in range(iters):
        gN = g.reshape(N, n * n) @ Nb.T                       # (N, q)
        Jm = np.einsum('me,mq->meq', C[:, k:], gN).reshape(N, e * q)
        H = Jm.conj().T @ Jm; gr = Jm.conj().T @ r
        while True:
            step = np.linalg.solve(H + lam * np.eye(e * q) * (1 + np.diag(H).real.mean()), -gr)
            Y2 = orth(Y + step.reshape(e, q)); r2, g2 = res(Y2); c2 = np.vdot(r2, r2).real
            if c2 < cost or lam > 1e8: break
            lam *= 4
        if c2 >= cost: break
        Y, r, g, cost = Y2, r2, g2, c2; lam = max(lam / 3, 1e-12)
        if cost < 1e-22: break
    return cost, np.concatenate([D, (Y @ Nb).reshape(e, n, n)])
if __name__ == '__main__':
    z = np.exp(2j * np.pi / 5); u = z ** np.arange(5)
    W = [np.array([1, -1, 0, 0, 0]), np.array([0, 1, -1, 0, 0]), np.array([0, 0, 1, -1, 0])]
    D3 = np.array([np.outer(u, w) for w in W]).astype(complex)
    Nb = ext_space(D3); print('ext space dim (beyond D):', len(Nb))
    for e in range(1, 7):
        best = 1e9
        for s in range(int(sys.argv[1])):
            c, B = extend(D3, e, s, Nb=Nb); best = min(best, c)
            if c < 1e-15: np.save(f'ext_D3_{e}.npy', B); break
        print('k=3 + e =', e, ' d =', 3 + e, ' best cost %.2e' % best, flush=True)
        if best > 1e-15: break
