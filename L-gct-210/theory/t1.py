import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lvl import *
random.seed(1)
n=5
# known 2n-3: last row x (sum 0 off corner), last col y, corner -sum y
B=[]
for j in range(3): B.append(add(E(4,j,n),E(4,3,n,-1)))
for i in range(4): B.append(add(E(i,4,n),E(4,4,n,-1)))
print('known7 level',is_level(B,n),'rank',rank(B))
T=tangent(B,n); print('dim T(L)',len(T), 'rank L+T', rank(B+T))
# exotic 4x5 (L-gct-180) as 5x5 with zero last row: rows0-2 exotic, row 3 free sum zero
def exo(rows,cols,n=5):
    a,b,c,d=cols; r0,r1,r2=rows
    b1=add(E(r0,a,n),E(r0,b,n,-1),E(r1,a,n,W),E(r1,b,n,-W),E(r2,a,n,W2),E(r2,b,n,-W2))
    b2=add(E(r0,c,n),E(r0,d,n,-1),E(r1,c,n,W2),E(r1,d,n,-W2),E(r2,c,n,W),E(r2,d,n,-W))
    return [b1,b2]
X=exo((0,1,2),(0,1,2,3))
for j in range(4): X.append(add(E(3,j,n),E(3,4,n,-1)))
print('exotic6 level',is_level(X,n),'rank',rank(X))
T=tangent(X,n); print('dim T(L)',len(T),'rank L+T',rank(X+T))
X2=exo((0,1,2),(0,1,2,3)); print('exo2 level',is_level(X2,n)); T=tangent(X2,n); print('dim T',len(T))
