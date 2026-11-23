import sys, numpy as np
for f in sys.argv[1:]:
    B = np.load(f); d, n, _ = B.shape
    phi = np.hstack([B.sum(axis=2), B.sum(axis=1)])   # (d, 2n)
    s = np.linalg.svd(phi, compute_uv=False); m = int((s > 1e-7).sum())
    supp = (abs(B).max(axis=0) > 1e-7).astype(int)
    rows = [np.linalg.matrix_rank(B[:, i, :], 1e-7) for i in range(n)]
    cols = [np.linalg.matrix_rank(B[:, :, j], 1e-7) for j in range(n)]
    print(f, 'd', d, 'm = dim phi(L)', m, 'k = dim L cap DC', d - m, 'row proj dims', rows, 'col proj dims', cols)
    print(supp)
