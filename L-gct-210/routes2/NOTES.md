# L-gct-210 routes2 notes (second agent; different routes than theory/NOTES.md)

Started. Plan: (0) numerically probe the true maximum (is 8 or 9 reachable? a dim-9 space would
refute the step); (1) gradient-span route; (2) row-restriction induction with rectangular
permanents; (3) literature.

Reformulation: M = C J (+) L, per|_M = 120 s^5 (fifth power of a linear form). Conditions on L:
sigma_k = 0, k = 1..5; gradient form: L perp span{grad per(J+t): t in L} = span of J, A L,
grad sigma_3(L), ...

## Finding 1 (verified exactly, ident.py): sigma_2 and sigma_3 are DIAGONAL in suitable linear forms
On sigma_1 = 0, with r_i, c_j row/column sums of t and s_ij = t_ij - (r_i + c_j)/2:
  2 sigma_2 = sum_ij s_ij^2 - (n/4)(sum r_i^2 + sum c_j^2)
  sigma_3   = (2/3) sum_ij s_ij^3 + ((n-2)/12)(sum r_i^3 + sum c_j^3)
(t -> s is invertible for n != 2.) So L embeds in C^35 (coordinates s, r, c) inside a diagonal
quadric and a diagonal (Fermat-type) cubic. sigma_4 is not diagonal (Gram terms <t_a,t_b><t_c,t_d>).
Consequence: grad sigma_3(a) = T^t(2 s.s, (3/4) r.r, (3/4) c.c) (Hadamard squares), all in L^perp.

## Numerical search (lm.py): complex Gauss-Newton on per(J + sum c_i B_i) = n! at sampled c
Works for n=3 d=3; for n=4 it does NOT find the known d=5 spaces from random starts (local
minima), so it cannot be used to refute or support "<= 8". Not pursued for unrestricted supports.

## Finding 2: the whole difficulty is L cap DC
Let phi = (row sums, column sums), m = dim phi(L) <= 8 (image lies in {sum r = sum c = 0} once
sigma_1 = 0 ... in fact sum r = sum c = 0 gives m <= 8), k = dim(L cap DC), d = k + m.
So "L cap DC = 0  =>  d <= 8" is a 20-line Lean proof (rank-nullity), and the step is equivalent to
  k + m <= 8 for every level space,
i.e. each doubly centred member must cost one dimension of phi(L). All extremal examples found
have k = 0, m = 7: row+col (L-gct-189 type) and a new type "two rows + one column"
(found_5_2_1_7.npy, lm.py with support mask; row projections 4,3,1,1,1, column 4,2,2,2,2).

Conditions a doubly centred member v in D = L cap DC imposes on the rest (from Finding 1, exact):
with Lam = s(L) (s-coordinates, dim d), for all v, v' in D and t, t' in L
  sum v.s(t) = 0,   sum v.v'.s(t) = 0,   sum v.s(t).s(t') = 0
(D + D.D is Euclid-orthogonal to Lam; Lam is isotropic for every diagonal form diag(v)).
Hence d <= 25 - dim(D + D.D). With a Kneser-type bound dim(D.D) >= 2k - 1 (repo has Kneser helpers
for Schur products) this gives d <= 26 - 3k; combined with d <= 8 + k it yields again only d <= 12
(worst case k = 4, 5). So the degree <= 3 information, used linearly, reproduces 12. FAILS as a proof.

## Route: gradient span (L perp grad per(J+t), t in L)
G = span{grad sigma_j(t)} lies in L^perp, so d <= 25 - dim G. Measured (gspan.py, numeric):
 row+col d=7:      dims of J, +A L, +G_3, +G_4, +G_5 cumulative = 1, 8, 17, 17, 17  (25-d = 18)
 2row+1col d=7:    1, 8, 17, 17, 17
 n=4 row+col d=5:  1, 6, 10, 10
An inequality dim(J + A L + G_3) >= 2d + 1 + (something >= 7 when d >= 9) would prove the step, but
G_3 = 0 for one-row spaces, so no uniform lower bound on G_3 exists: a structural dichotomy
(few-row/column spaces vs the rest) is unavoidable. FAILS as a short proof.

## Route: induction over a zero row (rectangular level spaces)
For t in L with row i zero, per(J+t) = sum_j per_4 of the 4x5 remainder: L_i = L cap {row i = 0}
is a level space of 4x5 rectangular matrices (sigma_1..sigma_4 = 0), dim L_i = d - a_i with
a_i = dim (row-i projection of L). Examples show a_i = 1 for most rows of extremal spaces, so the
natural recursion is d(m,n) <= d(m-1,n) + 1 in the "thin row" case, with conjectural values
d(m,5) = m + 2 (m >= 2), d(1,5) = 4. The complementary case (all row and column projections >= 2)
needs its own bound and nothing checked upstream covers rectangular or 5-wide shapes (217 is 4x4
row-centred <= 5, 216 is 4x4 doubly centred). Not a reduction to checked lemmas. FAILS (no base).

## Route: torus degeneration / initial subspaces
M = C J + L has per|_M = 120 l^5. Degenerating by row/column scalings gives a coordinate subspace
on which per = 0 (a multilinear polynomial is a 5th power only if 0), i.e. d + 1 <= 20. J is not
torus-fixed, so the level structure is lost in the limit. FAILS (bound 19).

## Route: pencils of quadrics
L is isotropic for A and for all polars sigma_3(a,.,.), a in L (in s-coordinates: diagonal forms).
Two generic quadrics on a 24-dim space still admit 11-dim common isotropic spaces; a count needs
>= 4 generic quadrics to exclude dim 9 and genericity cannot be shown for unknown L. FAILS.

## Doubly centred side
DC level spaces exist with k = 3: u (x) W, u = (1, z, z^2, z^3, z^4) (z a 5th root of unity; p1..p4(u)=0),
W = {w : sum w = 0, w_5 = 0}. Its first-order extension space is 12-dim, but numerically (ext2.py)
it extends by 1 (d = 4, m = 1) and not by 2 in 8 starts. Consistent with k + m <= 8, far from tight.

## Literature
Chan-Ilten, "Fano schemes of determinants and permanents" (ANT 9:3, 2015): linear spaces inside
{per = 0}; permanental-rank bound dim <= k n (arXiv 2308.14526 and related). Nothing found on
affine-linear spaces through J in a level set of per (the per(J+t) = n! problem), nor a 5x5 bound.

## Status at end of session
No mergeable proof route found. Masked searches for d = 8 (supports 2 rows+1 col, 2+2, 3+1, 3+2,
3+3) and d = 9 (2+2) were started in the background (masks.py -> masks.log); a line "FOUND 5 .. 8"
would show the bound 8 is attained, "FOUND 5 2 2 9" would refute the step. Unfinished when the
report was written; the search is unreliable for non-existence (local minima).
Most promising remaining plan (large): prove k + m <= 8 by a structural analysis of D = L cap DC
using the three exact orthogonality conditions of Finding 2 plus sigma_4; k = 0 is trivial.
