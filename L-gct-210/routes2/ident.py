# check: on sigma_1 = 0, with s_ij = t_ij - (r_i + c_j)/2:
#   2 sigma_2 = sum s^2 - (n/4)(sum r^2 + sum c^2)
#   sigma_3  = (2/3) sum s^3 + ((n-2)/12)(sum r^3 + sum c^3)
import random, itertools
from fractions import Fraction as F
def sig(t, n, k):
    tot = 0
    for R in itertools.combinations(range(n), k):
        for Cc in itertools.permutations(range(n), k):
            p = 1
            for a, b in zip(R, Cc): p *= t[a][b]
            tot += p
    return tot
for n in (3, 4, 5):
    for trial in range(3):
        t = [[F(random.randint(-9, 9)) for _ in range(n)] for _ in range(n)]
        S = sum(map(sum, t)); t[0][0] -= S
        r = [sum(t[i]) for i in range(n)]; c = [sum(t[i][j] for i in range(n)) for j in range(n)]
        s = [[t[i][j] - (r[i] + c[j]) / 2 for j in range(n)] for i in range(n)]
        p = lambda k: sum(x ** k for row in s for x in row)
        e2 = 2 * sig(t, n, 2) - (p(2) - F(n, 4) * (sum(x * x for x in r) + sum(x * x for x in c)))
        e3 = sig(t, n, 3) - (F(2, 3) * p(3) + F(n - 2, 12) * (sum(x ** 3 for x in r) + sum(x ** 3 for x in c)))
        print(n, e2, e3)
