import sys,os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, chk
z = np.exp(2j*np.pi/5); w = z**np.arange(5)
E = np.eye(4)
B0 = [np.outer(E[i], w) for i in range(4)]
print('C4xw', chk.level_err(B0))
for a in [2,3,4]:
    B = B0 + [np.outer(E[i], w**a) for i in range(4)]
    print(a, [chk.homog(B, k) for k in range(1,5)])
