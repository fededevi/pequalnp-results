import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm, gspan
def rk(X, tol=1e-7):
    s = np.linalg.svd(X, compute_uv=False); return int((s > tol).sum())
gspan.rk = rk
z = np.exp(2j * np.pi / 5); u = z ** np.arange(5)
W = [np.array([1, -1, 0, 0, 0]), np.array([0, 1, -1, 0, 0]), np.array([0, 0, 1, -1, 0])]
D3 = np.array([np.outer(u, w) for w in W]).astype(complex)
gspan.analyse(D3, 'u(x)W k=3'); gspan.analyse(D3[:1], 'u w^T k=1')
u2 = z ** (2 * np.arange(5))
D6 = np.array([np.outer(u, w) for w in W] + [np.outer(u2, w) for w in W]).astype(complex)
gspan.analyse(D6, 'u(x)W + u2(x)W')
gspan.analyse(gspan.rowcol(5), 'rowcol'); gspan.analyse(np.load('found_5_2_1_7.npy'), '2row+1col')
