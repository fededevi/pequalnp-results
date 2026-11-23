import numpy as np, itertools, sys
def setup(n):
    perms = np.array(list(itertools.permutations(range(n))))
    return perms
def per_and_grad(M, perms):
    # M: (N,n,n) complex. returns per (N,), grad (N,n,n)
    N, n, _ = M.shape
    rows = np.arange(n)
    E = M[:, rows[None, :], perms]          # (N, P, n)
    per = E.prod(axis=2).sum(axis=1)
    grad = np.zeros_like(M)
    for i in range(n):
        others = np.delete(E, i, axis=2).prod(axis=2)   # (N,P)
        for j in range(n):
            grad[:, i, j] = others[:, perms[:, i] == j].sum(axis=1)
    return per, grad
def run(n, d, seed, N=None, iters=200, verbose=False, B0=None, fixed=0, mask=None):
    rng = np.random.default_rng(seed)
    perms = setup(n)
    import math
    neq = sum(math.comb(d + k - 1, k) for k in range(1, n + 1))
    N = N or int(1.5 * neq) + 50
    B = (rng.normal(size=(d, n, n)) + 1j * rng.normal(size=(d, n, n))) * 0.5
    if B0 is not None: B[:len(B0)] = B0
    C = (rng.normal(size=(N, d)) + 1j * rng.normal(size=(N, d)))
    C *= rng.uniform(0.3, 1.5, size=(N, 1)) / np.sqrt(d)
    lam = 1e-2; f = math.factorial(n)
    def res(B):
        M = 1 + np.einsum('md,dij->mij', C, B)
        p, g = per_and_grad(M, perms)
        return p - f, g
    if mask is None: mask = np.ones((n, n))
    mi = np.flatnonzero(np.tile(mask.reshape(-1), d)); B = B * mask
    Q, _ = np.linalg.qr(B.reshape(d, -1).T); B = Q.T.reshape(d, n, n)
    r, g = res(B); cost = np.vdot(r, r).real
    for it in range(iters):
        Jm = np.einsum('md,mij->mdij', C, g).reshape(N, d * n * n)
        Jm = Jm[:, mi]
        H = Jm.conj().T @ Jm; gr = Jm.conj().T @ r
        while True:
            step = np.linalg.solve(H + lam * np.eye(H.shape[0]) * (1 + np.diag(H).real.mean()), -gr)
            B2 = B.copy().reshape(-1); B2[mi] += step; B2 = B2.reshape(d, n, n)
            Q, _ = np.linalg.qr(B2.reshape(d, -1).T); B2 = Q.T.reshape(d, n, n)
            # renormalise: orthonormalise basis to keep it nondegenerate
            r2, g2 = res(B2); c2 = np.vdot(r2, r2).real
            if c2 < cost or lam > 1e8: break
            lam *= 4
        if c2 < cost:
            B, r, g, cost = B2, r2, g2, c2; lam = max(lam / 3, 1e-12)
        else: break
        if verbose and it % 10 == 0: print(it, cost, lam, flush=True)
        if cost < 1e-22: break
    sv = np.linalg.svd(B.reshape(d, -1), compute_uv=False)
    return cost, sv, B
if __name__ == '__main__':
    n, d = int(sys.argv[1]), int(sys.argv[2]); seeds = range(int(sys.argv[3]), int(sys.argv[4]))
    for s in seeds:
        cost, sv, B = run(n, d, s)
        print(n, d, s, 'cost %.3e' % cost, 'sv min/max %.3e %.3e' % (sv[-1], sv[0]), flush=True)
