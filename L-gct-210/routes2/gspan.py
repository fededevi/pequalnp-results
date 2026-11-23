import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm, itertools
def rk(X, tol=1e-8):
    s = np.linalg.svd(X, compute_uv=False); return int((s > tol * s[0]).sum())
def analyse(B, name):
    d, n, _ = B.shape; perms = lm.setup(n); rng = np.random.default_rng(1)
    # gradients of homogeneous parts: sample per(J*z + t) gradient at several z, separate by Vandermonde
    N = 400
    C = rng.normal(size=(N, d)) + 1j * rng.normal(size=(N, d))
    T = np.einsum('md,dij->mij', C, B)
    zs = np.exp(2j * np.pi * np.arange(n) / n)   # n-th roots of unity
    G = []
    for z in zs:
        p, g = lm.per_and_grad(z + T, perms); G.append(g)
    G = np.array(G)                                # (n, N, n, n); grad = sum_k z^(n-k) * c_k * grad sigma_k
    parts = {}
    for k in range(1, n + 1):                      # coefficient of z^(n-k)
        P = np.einsum('z,zmij->mij', zs ** (-(n - k)), G).reshape(N, n * n) / n
        mx = abs(P).max(); parts[k] = P / mx if mx > 1e-8 else np.zeros_like(P)
    lvl = max(abs(lm.per_and_grad(1 + T, perms)[0] - np.prod(range(1, n + 1))))
    acc = np.zeros((0, n * n)); out = []
    for k in range(1, n + 1):
        acc = np.vstack([acc, parts[k]]); out.append(rk(acc))
    print(name, 'd =', d, 'level err %.1e' % lvl, 'cumulative dim of span grad sigma_1..k:', out,
          ' each:', [rk(parts[k]) for k in range(1, n + 1)], ' 25-d =', n * n - d)
def rowcol(n):
    B = []
    for j in range(n - 2):
        b = np.zeros((n, n), complex); b[n - 1, j] = 1; b[n - 1, n - 2] = -1; B.append(b)
    for i in range(n - 1):
        b = np.zeros((n, n), complex); b[i, n - 1] = 1; b[n - 1, n - 1] = -1; B.append(b)
    return np.array(B)
if __name__ == '__main__':
    analyse(rowcol(5), 'row+col n=5'); analyse(rowcol(4), 'row+col n=4')
    for f in sys.argv[1:]: analyse(np.load(f), f)
