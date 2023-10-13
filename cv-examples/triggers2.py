from z3 import *

# Example demonstrating multipatterns
s = Solver()
s.set(auto_config=False, mbqi=False)

f = Function('f', IntSort(), IntSort())
g = Function('g', IntSort(), IntSort())

a, x, y, z = Ints('a x y z')

# Trigger only when f(x) AND g(x) show up in the formula for the same x
s.add(ForAll([x], And(f(x) == x, g(x) == x), patterns=[MultiPattern(f(x), g(x))]))
# On the other hand, the following quantifier would trigger if f(x) OR g(x) show up in the formula.
# s.add(ForAll([x], And(f(x) == x, g(x) == x), patterns=[MultiPattern(f(x), g(x))]))


# s.add(f(1) == 2)  # unknown, quantifier not triggered because no g(x)
# s.add(And(f(1) == 2, g(1) == 2))  # unsat
# s.add(And(f(1) == 2, g(2) == 3))  # unknown, quantifier not triggered because g(x) for different x

# mathieu
# s.add(f(1) == 1, g(1) == 1)



print(s.check())
