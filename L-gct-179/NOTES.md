# L-gct-179: 7-dim level space for 4x5 rectangular permanent sum P(t) = sum_{f inj} prod (1+t_{i,f(i)}) = 120
Observation: P(t) = per_5 of the 5x5 matrix J + [t; 0] (last row zero). So this is a 5x5 level space
inside {row 5 = 0}. P = sum_k (5-k)! e_k(t), e_k = sum over k-matchings. Need e_1..e_4 = 0 on L.
Known: row+column (row 1 and column 1 support, A=0, a11+B=0) gives 6.
Search: lm4x5.py (LM on basis B in C^{7x4x5}, residual P(sum c_i B_i)-120 at sampled c).

## Fourier (column-frequency) graded ansatz
Write t = sum_a y^a (x) w^a, w^a_j = z^(a j), z = e^(2 pi i/5). Column shifts act by z^a on y^a,
so graded L = sum_a Y_a (x) w^a are natural. e_k expands with coefficients
F(a_1..a_k) = sum_{inj f} z^(sum a_i f(i)) (F.py), nonzero only if sum a = 0 mod 5; values integer.
Example: C^4 (x) w (all of frequency 1) is a 4-dim level space (e_k(x(x)w) = k! e_k(x) e_k(w) = 0).
Graded constraints (exact, by hand): Y_0 = 0 (y0 would need e1..e4 = 0); (1,4): Y4 perp (J-I) Y1,
so n1+n4 <= 4, n2+n3 <= 4; n1 = 4 forces Y2 = Y3 = 0. Up to a -> u a (u in Z5*), d = 7 graded
needs (n1,n2,n3,n4) in {3301,3211,3121,3031,2302,2212}: gradedT.py searches these.
Unrestricted LM d=7 (lm2.py, d7_*.log): best ~0.24 after ~100 starts (none).
Results (30 LM starts each): all six graded d=7 cases fail (best cost ~2e3: clearly infeasible).
Joint eigenbasis of (4-cycle on rows) x (5-cycle on columns): 20 one-dim eigenspaces; exhaustive
enumeration of level coordinate subsets (enum20.py): max 4.
Masked (lm2 + mask, supports first r rows + first c columns), d=7: 2x1 best 1.5e2, 1x2 1.8e2, 2x2 3.2e1.
By hand: support row1 + cols 1,2 gives max 6 (Q = hyperbolic pairing via J-I, 4x4 invertible).
Row+col 6-space (rc6.npy) has a 1-dim first-order extension (v = rows (1,-1/4,-1/4,-1/4,-1/4)) but
L+v is not level; LM started near rc6+v (near.py) does not converge (cost >= 0.6).
Random d=7 LM (lm2.py, ~330 starts, d7_*.log): best cost 0.24, none. For comparison d=6 random
starts succeed ~30% (d6/B_*.npy; non-real, row projections e.g. 4,3,3,3 -- not the row+col type).
grow7.py: start d=7 from each d=6 solution + best first-order extension direction: best ~0.47-0.54.
The d=6 random solutions have gradient matrix rank 14 up to a small sv (~1e-6, shrinking slowly as
cost drops), i.e. possibly a 1-dim first-order extension, but no second-order one found.
symsearch.py: L invariant under one (row perm, col perm) element, eigenspace dims sampled (sym7.log).
rmask.py: random support masks (11-17 entries), d=7 (rmask_*.log).

## Final status (end of ~2h budget): NO witness for d = 7
- Random unrestricted LM d=7: 788 starts (d7_*.log), best cost 0.24.
- Graded (column-frequency) d=7: all 6 admissible cases x 30 starts, best ~2e3 (infeasible).
- symsearch (one (row perm, col perm) symmetry, 34 conjugacy pairs x 8 eigen-compositions x 2): best 1.09.
- Random support masks 11-17 entries (729 masks x 2 starts): best 1.83. Row/col-block masks: best 2.3.
- Fixed sub-ansatz: L containing a full sum-zero row (rowfix.py): best 12.9; L containing C^4 (x) w
  (wfix.py): best 7.4e3.
- Growth from d=6 solutions (grow7.py): best 0.47.
Numerical evidence suggests 6 may be the maximum over C as well (consistent with the routes2
conjecture d(m,5) = m+2), but LM non-convergence does not prove non-existence. No Lean file written.
