import sys, os, glob; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np
from lm2 import P_and_grad
def ext_dim(B, n=300, seed=0):
    B = B.reshape(len(B), -1); d = len(B); rng = np.random.default_rng(seed)
    c = rng.normal(size=(n, d)) + 1j*rng.normal(size=(n, d))
    t = (c @ B).reshape(n, 4, 5)
    _, g = P_and_grad(1 + t)
    sv = np.linalg.svd(g.reshape(n, -1), compute_uv=False)
    sv = sv / sv[0]
    return int((sv > 1e-9).sum()), sv
if __name__ == '__main__':
    for f in sorted(glob.glob(sys.argv[1])):
        B = np.load(f); r, sv = ext_dim(B)
        print(f, 'rank grads', r, 'null', 20 - r, 'ext', 20 - r - len(B), np.round(np.log10(sv[r-2:r+2]),1))
