import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sat import *
random.seed(5); n=5
def block(rows, coefs, col):  # rows[i] gets coefs[i] at column col
    return add(*[E(r,col,n,c) for r,c in zip(rows,coefs)])
rowfree=lambda r:[add(E(r,j,n),E(r,4,n,-1)) for j in range(4)]
# S4: 4-block, u in span(x0,x1,x2), + free row 4
c4=[1,I4,P-1,P-I4]
S4=[block((0,1,2,3),c4,j) for j in range(3)]+rowfree(4)
ex,G,cs=report('S4 = 4-block(3 cols) + free row',S4,showex=True)
c5=[pow(Z5,k,P) for k in range(5)]
S5=[block((0,1,2,3,4),c5,j) for j in range(4)]
report('S5 = 5-block(4 cols)',S5,showex=True)
c3=[1,W,W2]
S3=[block((0,1,2),c3,j) for j in range(2)]
report('S3 = 3-block(2 cols)',S3,gb=False)
