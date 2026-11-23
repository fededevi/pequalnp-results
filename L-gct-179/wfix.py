import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lmF
T = lmF.T.copy()   # rows i*5+a = e_i (x) w^a ; put freq-1 rows first
order = [i*5+1 for i in range(4)] + [k for k in range(20) if k % 5 != 1]
T = T[order]
S = np.zeros((7, 20), bool)
for k in range(4): S[k, k] = True
for k in range(4, 7): S[k, 4:] = True
best = 1e9
for s in range(int(sys.argv[1])):
    c, X = lmF.run(S, s, T=T, iters=1500); best = min(best, c)
    print(s, '%.2e' % c, flush=True)
    if c < 1e-14: np.save('wfix_found.npy', X @ T); break
print('best', best)
