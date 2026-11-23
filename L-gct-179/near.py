import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm2
def echelon(B):
    import scipy.linalg as sl
    B = B.reshape(len(B), -1); _, _, p = sl.qr(B, pivoting=True)
    piv = np.array(sorted(p[:len(B)])); X = np.linalg.solve(B[:, piv], B)
    free = np.array([k for k in range(B.shape[1]) if k not in set(piv)])
    return piv, X[:, free]
if __name__ == '__main__':
    B0 = np.load(sys.argv[1]).reshape(-1, 20); v = np.load(sys.argv[2]).reshape(1, 20) if len(sys.argv) > 2 and sys.argv[2] != '-' else None
    if v is not None: B0 = np.vstack([B0, v])
    d = len(B0); rng = np.random.default_rng(0)
    for s in range(int(sys.argv[3]) if len(sys.argv) > 3 else 10):
        for eps in [1e-3, 1e-2, 1e-1, 0.3]:
            Bp = B0 + eps*(rng.normal(size=B0.shape) + 1j*rng.normal(size=B0.shape))
            piv, X = echelon(Bp)
            c, B, _, X = lm2.run(d, s, piv=piv, X0=X)
            print(s, eps, '%.3e' % c, flush=True)
            if c < 1e-18: np.save(f'near_found_{s}.npy', B); sys.exit()
