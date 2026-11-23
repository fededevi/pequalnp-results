import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, itertools, lmF
rows_cls = {'id': [0,1,2,3], 't': [1,0,2,3], 'tt': [1,0,3,2], 'c3': [1,2,0,3], 'c4': [1,2,3,0]}
cols_cls = {'id': [0,1,2,3,4], 't': [1,0,2,3,4], 'tt': [1,0,3,2,4], 'c3': [1,2,0,3,4],
            'c3t': [1,2,0,4,3], 'c4': [1,2,3,0,4], 'c5': [1,2,3,4,0]}
def perm_mat(p):
    M = np.zeros((len(p), len(p))); M[p, np.arange(len(p))] = 1; return M
def eig_blocks(pr, pc):
    G = np.kron(perm_mat(pr), perm_mat(pc))   # acts on vec(t) row-major (i*5+j)
    order = np.lcm.reduce([len(set(itertools.accumulate(range(1), lambda a,b:a)))] ) if False else 60
    # eigen-decomposition via projectors onto exp(2 pi i k/60)
    blocks = []
    for k in range(60):
        lam = np.exp(2j*np.pi*k/60)
        Pk = sum(np.linalg.matrix_power(G, m) * lam**(-m) for m in range(60)) / 60
        r = np.linalg.matrix_rank(Pk, 1e-8)
        if r:
            u, s, vh = np.linalg.svd(Pk); blocks.append((k, u[:, :r]))
    return blocks
def comps(blocks, d, rng, n):
    ks = [b[0] for b in blocks]; m = {b[0]: b[1].shape[1] for b in blocks}
    out = set(); tries = 0
    while len(out) < n and tries < 20000:
        tries += 1
        c = {k: 0 for k in ks}
        left = d
        for k in rng.permutation(ks):
            if left == 0: break
            v = rng.integers(0, min(m[k], left) + 1); c[k] = v; left -= v
        if left: continue
        ok = True
        for k in ks:
            kb = (-k) % 60
            if kb == k:
                lim = m[k] // 2 if k else (m[k] - 1) // 2 + (0)
                if c[k] > max(lim, 0) and k != 0: ok = False
                if k == 0 and c[k] > (m[k]) // 2: ok = False
            elif c[k] + c.get(kb, 0) > m[k]: ok = False
        if ok: out.add(tuple(sorted(c.items())))
    return [dict(c) for c in out]
if __name__ == '__main__':
    d = int(sys.argv[1]); ncomp = int(sys.argv[2]); ntry = int(sys.argv[3]); seed = int(sys.argv[4])
    rng = np.random.default_rng(seed)
    pairs = [(a, b) for a in rows_cls for b in cols_cls if (a, b) != ('id', 'id')]
    rng.shuffle(pairs)
    for a, b in pairs:
        blocks = eig_blocks(rows_cls[a], cols_cls[b])
        T = np.hstack([u for _, u in blocks]).T   # rows = eigen basis vectors (20 x 20)
        off = np.cumsum([0] + [u.shape[1] for _, u in blocks])
        for c in comps(blocks, d, rng, ncomp):
            S = []
            for bi, (k, u) in enumerate(blocks):
                for _ in range(c[k]):
                    row = np.zeros(20, bool); row[off[bi]:off[bi+1]] = True; S.append(row)
            best = 1e9
            for s in range(ntry):
                cost, X = lmF.run(np.array(S), s, T=T, iters=800); best = min(best, cost)
                if cost < 1e-14:
                    sv = np.linalg.svd(X, compute_uv=False)
                    print('FOUND', a, b, {k: v for k, v in c.items() if v}, cost, sv.min(), flush=True)
                    np.save(f'foundS_{a}_{b}_{seed}_{s}.npy', X @ T); break
            print(a, b, {k: v for k, v in c.items() if v}, 'best %.2e' % best, flush=True)
