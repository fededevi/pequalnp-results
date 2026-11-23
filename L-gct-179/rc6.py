import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import numpy as np, ext, chk
def E(i, j): m = np.zeros((4, 5)); m[i, j] = 1; return m
B = [E(0,1)-E(0,2), E(0,2)-E(0,3), E(0,3)-E(0,4), E(1,0)-E(0,0), E(2,0)-E(0,0), E(3,0)-E(0,0)]
B = np.array(B); print('level', chk.level_err(B)); print(ext.ext_dim(B)[0])
np.save('rc6.npy', B)
