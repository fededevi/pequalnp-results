import numpy as np, itertools
R, C = 4, 5
INJ = np.array([p for p in itertools.permutations(range(C), R)])
def P(t):  # t (N,4,5)
    return (1 + t)[:, np.arange(R)[None, :], INJ].prod(axis=2).sum(axis=1)
def level_err(B, n=200, seed=0):
    B = np.asarray(B).reshape(len(B), R, C); rng = np.random.default_rng(seed)
    c = rng.normal(size=(n, len(B))) + 1j*rng.normal(size=(n, len(B)))
    return np.abs(P(np.einsum('nd,dij->nij', c, B)) - 120).max()
def homog(B, k, n=60, seed=1):
    # max |degree-k part| via scaling interpolation
    B = np.asarray(B).reshape(len(B), R, C); rng = np.random.default_rng(seed)
    c = rng.normal(size=(n, len(B))) + 1j*rng.normal(size=(n, len(B)))
    t = np.einsum('nd,dij->nij', c, B)
    zs = np.exp(2j*np.pi*np.arange(5)/5)
    vals = np.array([P(z*t) for z in zs])   # (5,n)
    coef = np.fft.fft(vals, axis=0)/5  # coef index -k
    return np.abs(coef[k % 5]).max()
