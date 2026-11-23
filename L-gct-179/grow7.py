import sys, os, glob; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm2
from near import echelon
from ext import ext_dim
from lm2 import P_and_grad
done = set()
rng = np.random.default_rng(5)
while True:
    fs = [f for f in sorted(glob.glob('d6/*.npy')) if f not in done]
    if not fs: break
    f = fs[0]; done.add(f); B6 = np.load(f).reshape(6, -1)
    # best candidate 7th vector: smallest right singular vector of gradient matrix outside L
    c = rng.normal(size=(300, 6)) + 1j*rng.normal(size=(300, 6))
    _, g = P_and_grad(1 + (c @ B6).reshape(-1, 4, 5)); G = g.reshape(300, -1)
    _, sv, vh = np.linalg.svd(G); Q, _ = np.linalg.qr(B6.T)
    cands = vh[-8:].conj(); cands = cands - (cands @ Q.conj()) @ Q.T
    best = 1e9
    for s in range(6):
        v = cands[np.argsort(-np.linalg.norm(cands, axis=1))[0]] if s == 0 else cands[s % len(cands)] + 0.3*(rng.normal(size=20)+1j*rng.normal(size=20))
        B0 = np.vstack([B6, v / np.linalg.norm(v)])
        piv, X = echelon(B0 + 1e-3*rng.normal(size=B0.shape))
        cost, B, _, X = lm2.run(7, s, piv=piv, X0=X, iters=1500); best = min(best, cost)
        if cost < 1e-14: print('FOUND', f, s, cost, flush=True); np.save(f'grow_found_{os.path.basename(f)}', B); break
    print(f, 'log10 sv tail', np.round(np.log10(sv[-8:]/sv[0]), 1), 'best %.2e' % best, flush=True)
