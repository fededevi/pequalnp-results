import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from ext import *
random.seed(3); n=5
def exo(rows,cols,n=5):
    a,b,c,d=cols; r0,r1,r2=rows
    b1=add(E(r0,a,n),E(r0,b,n,-1),E(r1,a,n,W),E(r1,b,n,-W),E(r2,a,n,W2),E(r2,b,n,-W2))
    b2=add(E(r0,c,n),E(r0,d,n,-1),E(r1,c,n,W2),E(r1,d,n,-W2),E(r2,c,n,W),E(r2,d,n,-W))
    return [b1,b2]
X=exo((0,1,2),(0,1,2,3))
for j in range(4): X.append(add(E(3,j,n),E(3,4,n,-1)))
ex=complement(X,n); print('extra dirs',len(ex))
conds,cs=ext_conditions(X,ex,n)
for k in sorted(conds): print('deg',k,'num independent conditions',len(conds[k]))
polys=[q for k in sorted(conds) for q in conds[k]]
G=sp.groebner([q.as_expr() for q in polys],*cs,modulus=P,order='grevlex')
print(G.exprs)
