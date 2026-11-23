import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm2
from near import echelon
from ext import ext_dim
B = np.load(sys.argv[1]).reshape(6, -1)
for r in range(3):
    piv, X = echelon(B)
    c, B, _, _ = lm2.run(6, 100 + r, piv=piv, X0=X, iters=3000, N=600)
    print(r, 'cost %.2e' % c, np.round(np.log10(ext_dim(B)[1][10:16]), 1), flush=True)
np.save(sys.argv[1].replace('.npy', '_ref.npy'), B)
