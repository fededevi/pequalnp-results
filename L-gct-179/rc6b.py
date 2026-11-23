import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, chk
from lm2 import P_and_grad
B = np.load('rc6.npy').reshape(6, -1); rng = np.random.default_rng(0)
c = rng.normal(size=(300, 6)) + 1j*rng.normal(size=(300, 6))
_, g = P_and_grad(1 + (c @ B).reshape(-1, 4, 5)); G = g.reshape(300, -1)
u, s, vh = np.linalg.svd(G); N = vh[13:].conj()   # null space (7 x 20)
# remove L component
Q, _ = np.linalg.qr(B.T); s7 = N - (N @ Q.conj()) @ Q.T
k = np.argmax(np.linalg.norm(s7, axis=1)); v = s7[k]; v = v / v[np.argmax(abs(v))]
print(np.round(v.reshape(4, 5), 4))
print('level with v', chk.level_err(np.vstack([B, v])))
for k in range(1,5): print(k, chk.homog(np.vstack([B, v]), k))
np.save('rc6_v.npy', v)
