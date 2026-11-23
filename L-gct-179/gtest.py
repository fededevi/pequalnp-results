import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, lmF
for freqs in [[1,1,1,1],[1,1,1,4],[1,1,4,4],[1,1,1,2],[1,1,2,3]]:
    print(freqs, ['%.1e' % lmF.run(lmF.graded_S(freqs), s, iters=500)[0] for s in range(3)], flush=True)
