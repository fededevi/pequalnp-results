import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sat import *
random.seed(6); n=5
def block(rows, coefs, col): return add(*[E(r,col,n,c) for r,c in zip(rows,coefs)])
rowfree=lambda r:[add(E(r,j,n),E(r,4,n,-1)) for j in range(4)]
c3=[1,W,W2]
# seed 2: 3-block(2 cols) + free row 3  (block totally invisible)
S=[block((0,1,2),c3,j) for j in range(2)]+rowfree(3)
report('3-block(cols 0,1) + free row 3',S)
# seed 3: two 2-blocks + free row
S=[block((0,1),[1,-1],0),block((2,3),[1,-1],1)]+rowfree(4)
report('2-blocks(col0),(col1) + free row 4',S)
S=[block((0,1),[1,-1],0),block((2,3),[1,-1],0)]+rowfree(4)
report('2-blocks(col0),(col0) + free row 4',S)
# seed 5: 3-block + 2-block
S=[block((0,1,2),c3,j) for j in range(2)]+[block((3,4),[1,-1],2)]
report('3-block(cols 0,1) + 2-block(col 2)',S)
S=[block((0,1,2),c3,j) for j in range(2)]+[block((3,4),[1,-1],0)]
report('3-block(cols 0,1) + 2-block(col 0)',S)
