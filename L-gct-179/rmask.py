import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm2
seed = int(sys.argv[1]); rng = np.random.default_rng(seed)
for trial in range(10000):
    k = rng.integers(11, 18)
    m = np.zeros(20); m[rng.choice(20, k, replace=False)] = 1; m = m.reshape(4, 5)
    best = 1e9
    for s in range(2):
        c, B, piv, X = lm2.run(7, s, mask=m, iters=600); best = min(best, c)
        if c < 1e-14: print('FOUND', m.astype(int).tolist(), c, flush=True); np.save(f'rmask_found_{seed}_{trial}.npy', B); break
    print(trial, k, 'best %.2e' % best, m.astype(int).tolist(), flush=True)
