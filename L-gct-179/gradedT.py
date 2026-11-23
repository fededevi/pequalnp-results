import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lmF
cases = [tuple(map(int, c)) for c in sys.argv[2:]]   # n1n2n3n4 strings
tries = int(sys.argv[1])
for cs in cases:
    freqs = [a+1 for a in range(4) for _ in range(cs[a])]
    best = 1e9
    for s in range(tries):
        c, X = lmF.run(lmF.graded_S(freqs), s); best = min(best, c)
        if c < 1e-18:
            sv = np.linalg.svd(X, compute_uv=False); print('FOUND', cs, s, c, sv.min(), flush=True)
            np.save('foundG_%s_%d.npy' % (''.join(map(str, cs)), s), X); break
    print(cs, 'best %.3e' % best, flush=True)
