from z3 import *

# Trigger instantiation exercise in Z3

s = Solver()
s.set(auto_config=False, mbqi=False)

f = Function('f', IntSort(), IntSort())
fp = Function('fp', IntSort(), IntSort())
g = Function('g', IntSort(), IntSort())
P = Function('P', IntSort(), IntSort(), BoolSort())

a, x, y, z = Ints('a x y z')

s.add(y == f(a))
s.add(z == g(y))
s.add(Not(P(a, z)))

s.add(ForAll([x], And(f(x) == x + 1, f(x) == fp(x)), patterns=[f(x)]))
s.add(ForAll([x], g(fp(x)) == x, patterns=[g(fp(x))]))
s.add(ForAll([x], P(x, x), patterns=[P(x, x)]))

print(s.check())  # unsat