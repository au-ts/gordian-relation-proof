from z3 import *

x = Bool('x')
y = Bool('y')
z = Bool('z')


F = Implies(x, y)
F = And(F, z == z)  # <==>

print(F)

print(solve(F))

print(solve(Not(F)))





