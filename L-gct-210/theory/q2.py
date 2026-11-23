"""Exact rank/signature of sigma_2 (sum of 2x2 subpermanents) on H = {sigma_1 = 0} and on the doubly
centred space DC, n = 3, 4, 5.  sigma_2(t) = sum_{i<i', j != j'} t_ij t_i'j'."""
import sympy as sp
from itertools import product
def gram(n):
    N = n * n; A = sp.zeros(N, N)   # sigma_2(t) = 1/2 t^T A t
    for i, j, k, l in product(range(n), repeat=4):
        if i != k and j != l: A[i * n + j, k * n + l] = 1
    return A
for n in (3, 4, 5):
    A = gram(n); N = n * n
    ones = sp.Matrix([[1] * N])
    H = ones.nullspace()                                   # sigma_1 = 0
    rows = [[1 if a // n == i else 0 for a in range(N)] for i in range(n)]
    cols = [[1 if a % n == j else 0 for a in range(N)] for j in range(n)]
    DC = sp.Matrix(rows + cols).nullspace()
    out = [n]
    for name, Bs in (('H', H), ('DC', DC)):
        Bm = sp.Matrix.hstack(*Bs); G = Bm.T * A * Bm
        ev = G.eigenvals()
        # signature via Sylvester: congruent diagonalisation by eigenvalues of the symmetric rational matrix
        pos = sum(m for e, m in ev.items() if e > 0); neg = sum(m for e, m in ev.items() if e < 0)
        out.append((name, 'dim', len(Bs), 'rank', G.rank(), 'signature', (pos, neg)))
    # eigenvalues of A itself
    out.append(('eig A', A.eigenvals()))
    print(*out)
    print('   isotropic bound on H: dim <=', (N - 1) - sp.ceiling(sp.Rational(N - 1, 2)), '; known max: 3 (n=3), 2n-3 lower bound', 2 * n - 3)
