import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lm2
d = int(sys.argv[1]); tries = int(sys.argv[2])
for spec in sys.argv[3:]:
    nr, nc = map(int, spec.split('x'))
    m = np.zeros((4, 5)); m[:nr, :] = 1; m[:, :nc] = 1
    if m.sum() < d: continue
    best = 1e9
    for s in range(tries):
        c, B, piv, X = lm2.run(d, s, mask=m); best = min(best, c)
        if c < 1e-18: print('FOUND', spec, s, c, flush=True); np.save(f'foundM_{spec}_{d}.npy', B); break
    print(spec, d, 'best %.3e' % best, flush=True)
