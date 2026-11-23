import numpy as np, glob
for f in sorted(glob.glob('foundF_*.npy')):
    X = np.load(f); print(f, np.round(np.linalg.svd(X, compute_uv=False), 4))
