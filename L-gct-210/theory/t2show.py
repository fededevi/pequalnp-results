from lvl import *
NAMES=(('',1),('w',W),('w2',W2),('i',I4),('z',Z5),('z2',Z5**2%P),('z3',Z5**3%P),('z4',Z5**4%P))
def fmt(x):
    if x%P==0: return '0'
    for d in (1,2,3,4,5,6):
        for a in range(-12,13):
            for nm,c in NAMES:
                if a and (a*c-x*d)%P==0: return f'{a}{nm}'+(f'/{d}' if d>1 else '')
    return '?'
def show(v,n=5):
    for i in range(n): print('   ',' '.join(f'{fmt(v[i*n+j]):>7}' for j in range(n)))
