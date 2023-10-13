from z3 import *

X = IntVector('x', 6) 

# XKCD example
s = Solver()

c = X[0] * 215 + X[1] * 275 + X[2] * 335 + X[3] * 355 + X[4] * 420 + X[5] * 580 == 1505

for i in range(6):
    s.add(X[i] >= 0)

s.add(c)

while s.check() == sat:
    m = s.model()
    print(m)
    s.add(Or([X[i] != m[X[i]] for i in range(6)]))


