import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm
def mk(n, rows, cols):
    m = np.zeros((n, n)); m[rows, :] = 1; m[:, cols] = 1; return m
n = int(sys.argv[1]); nr = int(sys.argv[2]); nc = int(sys.argv[3]); d = int(sys.argv[4]); tries = int(sys.argv[5])
m = mk(n, list(range(nr)), list(range(nc)))
best = 1e9
for s in range(tries):
    c, sv, B = lm.run(n, d, s, mask=m, iters=300)
    best = min(best, c)
    if c < 1e-15: print('FOUND', n, nr, nc, d, s, c); np.save(f'found_{n}_{nr}_{nc}_{d}.npy', B); break
print(n, nr, nc, d, 'best', best)
