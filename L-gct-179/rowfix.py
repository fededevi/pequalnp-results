import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lmF
def E(i, j): m = np.zeros(20); m[i*5+j] = 1; return m
T = [E(0, j) - E(0, 4) for j in range(4)] + [E(0, 4)] + [E(i, j) for i in range(1, 4) for j in range(5)]
T = np.array(T, complex)
S = np.zeros((7, 20), bool)
for k in range(4): S[k, k] = True
for k in range(4, 7): S[k, 4:] = True
best = 1e9
for s in range(int(sys.argv[1])):
    c, X = lmF.run(S, s, T=T, iters=1500); best = min(best, c)
    print(s, '%.2e' % c, flush=True)
    if c < 1e-14: np.save('rowfix_found.npy', X @ T); break
print('best', best)
