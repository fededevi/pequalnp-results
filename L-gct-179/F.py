import numpy as np, itertools
z = np.exp(2j*np.pi/5)
for k in range(1,5):
    for a in itertools.combinations_with_replacement(range(5), k):
        if sum(a) % 5: continue
        F = sum(z**(sum(ai*fi for ai, fi in zip(a, f))) for f in itertools.permutations(range(5), k))
        if abs(F) > 1e-9: print(k, a, np.round(F, 6))
