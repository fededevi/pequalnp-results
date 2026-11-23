# L-gct-210 theory notes (n = 5, claim dim L <= 8)

## sigma_2 rank / signature (q2.py re-run, exact sympy)
Gram matrix of sigma_2 on C^{n x n} (sigma_2 = 1/2 t^T A t): A = (J - I) (x) (J - I),
eigenvalues (n-1)^2 (x1), -(n-1) (x 2(n-1)), 1 (x (n-1)^2). Nondegenerate on the whole space;
explicit inverse A^{-1} = (J/(n-1) - I) (x) (J/(n-1) - I).

| n | H = {sigma_1=0}: dim, rank, sig | DC (doubly centred): dim, rank, sig | Witt bound on H | Witt bound on DC | known lower |
|---|---|---|---|---|---|
| 3 | 8, 8, (4,4) | 4, 4, (4,0) | 4 | 2 | 3 (= max, L-gct-094) |
| 4 | 15, 15, (9,6) | 9, 9, (9,0) | 7 | 4 | 5 |
| 5 | 24, 24, (16,8) | 16, 16, (16,0) | **12** | **8** | 7 |

Closed form: on H, 2 sigma_2 = sum t^2 - sum r_i^2 - sum c_j^2 (r, c row/column sums); on DC
sigma_2 = 1/2 sum t_ij^2 (nondegenerate over C, positive definite over R).

## Does the isotropic bound plus the reduction give <= 8?  NO.
- The reduction L-gct-092 (Gct/L092.lean) does NOT preserve dimension: it gives
  dim L <= G + 2n, where G bounds doubly centred level spaces (rank-nullity on
  phi = (row sums, column sums); best possible version G + 2n - 2, as sigma_1 = 0 forces
  sum r = sum c = 0). With G = 8: dim L <= 18 (or 16). Useless.
- sigma_1 = 0 alone only puts L in H (dim 24); sigma_2 is nondegenerate there with Witt index 12,
  so the isotropic bound is dim L <= 12. It is sharp for sigma_2 alone (Witt: 12-dim totally
  isotropic subspaces of H exist), so sigma_1, sigma_2 cannot give 8.
- The doubly centred bound 8 is a bound on L cap DC only. Sanity check that DC is the wrong lens:
  for n = 4 the DC Witt bound is 4 < 5 = 2n-3 (achieved), so extremal spaces are not doubly centred.
  For n = 5 the known 7-dim space (last row x, last column y; kd.py in the scratchpad) has
  dim phi(L) = 7, dim(L cap DC) = 0: it lies entirely off DC.
- Orthogonal splitting H = DC (+) E (E = row/column-mean part, dim 8, sigma_2 = -4 x positive
  there): with k = dim(L cap DC), m = dim pi_E(L) <= 8, isotropy gives only k + m <= 12 and k <= 8.

## Lean feasibility
- Ceiling <= 8 via isotropy: impossible (bound is 12).
- What remains: exclude dim 9..12 using sigma_3, sigma_4, sigma_5. The n = 3 analogue (isotropic bound
  4, true max 3, gap 1) took 1658 lines (Helpers/LevelThree.lean: 16 charts, explicit ideal-membership
  certificates). For n = 5 the gap is 4; 9-planes in the isotropic Grassmannian of a 24-dim quadric form
  a 90-dim family, ~2^12 charts, quartic/quintic equations: not feasible as a certificate proof.
- Feasible by-product (not the step): `dim L <= 12` for n = 5 (in fact 2 dim L <= n^2 for all n) from
  A's explicit inverse: polar map injective, W <= W^perp, dim W + dim W^perp = n^2. Pattern exists in
  Helpers/BlockIsotropic.lean (n = 3, L-gct-055). ~150-250 lines.
- No proof route for <= 8 found; the conjecture's truth is not settled here (no counterexample sought).

## Existing Lagrangian method (L-gct-217, n = 4 row-centred <= 5)
217 works because there the gap is 1: row-centred 4x4 space has dim 12, Witt index 6, target 5;
at dim 6 the space is Lagrangian (L = L^perp), which yields explicit matrices in L, then sigma_3,
sigma_4 force a contradiction. For n = 5 the same trick only excludes the top case dim 12
(-> <= 11); dims 9, 10, 11 have L strictly inside L^perp and the trick gives nothing.
Possible mergeable sub-steps, not the step: "<= 12" (easy) and perhaps "<= 11" (217-style, large).
