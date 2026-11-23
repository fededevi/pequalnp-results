import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from lvl import *
random.seed(2)
n=5
def show(v):
    # print matrix with small ints / w-multiples recognised
    def f(x):
        for a in range(-9,10):
            for nm,c in (('',1),('w',W),('w2',W2)):
                if a and (a*c-x)%P==0: return f'{a}{nm}'
        for d in (2,3,4,5,6):
            for a in range(-12,13):
                for nm,c in (('',1),('w',W),('w2',W2)):
                    if a and (a*c-x*d)%P==0: return f'{a}{nm}/{d}'
        return '0' if x%P==0 else '?'
    for i in range(n): print('   ',' '.join(f'{f(v[i*n+j]):>7}' for j in range(n)))
def extra(B):
    T=tangent(B,n)
    # complement of L in T
    R,piv=rref(B)
    out=[]
    cur=B[:]
    for t in T:
        if rank(cur+[t])>rank(cur): out.append(t); cur.append(t)
    return out
B=[]
for j in range(3): B.append(add(E(4,j,n),E(4,3,n,-1)))
for i in range(4): B.append(add(E(i,4,n),E(4,4,n,-1)))
ex=extra(B)
for t in ex:
    # reduce modulo L for display
    R,piv=rref(B+[t]); t2=R[-1] if len(R)==8 else t
    full=rref(B+[t])[0]
    print('extra dir for known7 (rref rows of L+t):')
    for r in full: show(r); print()
    print('L+t level?',is_level(B+[t],n))
