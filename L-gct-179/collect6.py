import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm2
for s in range(int(sys.argv[1]), int(sys.argv[2])):
    c, B, piv, X = lm2.run(6, s)
    print(s, '%.2e' % c, flush=True)
    if c < 1e-12: np.save(f'd6/B_{s}.npy', B)
