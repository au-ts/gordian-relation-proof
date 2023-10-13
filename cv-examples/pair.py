from z3 import *

# Declare sort
Pair = DeclareSort('Pair')

# Declare all functions
pair = Function('pair', IntSort(), IntSort(), Pair)
fst = Function('fst', Pair, IntSort())
snd = Function('snd', Pair, IntSort())

# Variables to be used in quantifiers and in constraints
x, y, z, a = Ints('x y z a')
p = Const('p', Pair)
p2 = Const('p2', Pair)

s = Solver()
s.set(auto_config=False, mbqi=False)  # always set these options!

# Basic axioms: definitions of fst and snd. 
# s.add(ForAll([x, y], fst(pair(x, y)) == x, patterns=[fst(pair(x, y))]))
# s.add(ForAll([x, y], snd(pair(x, y)) == y, patterns=[snd(pair(x, y))]))
s.add(ForAll([x, y], fst(pair(x, y)) == x, patterns=[pair(x, y)]))
s.add(ForAll([x, y], snd(pair(x, y)) == y, patterns=[pair(x, y)]))

# These allow us to prove:
F = fst(pair(1, 2)) == 1

# If we change the triggers to just be pair(x, y) in both cases, we can also prove
# F = Not(pair(1, 2) == pair(2, 3))

# Alternatively, we can add another axiom:
# s.add(ForAll([x, y, z, a], (pair(x, y) == pair(z, a)) == And(z == x, a == y), 
#              patterns=[MultiPattern(pair(x, y), pair(z, a))]))
# This axiom is arguably worse than the above axioms with changed triggers, since it leads to more
# instantiations.

# Another alternative would be
# s.add(ForAll([p, p2], (p == p2) == And(fst(p) == fst(p2), snd(p) == snd(p2)), patterns=[unclear]))
# but there are no good trigger terms for this version.

# Additional axiom:
s.add(ForAll([p], p == pair(fst(p), snd(p)), patterns=[fst(p), snd(p)]))

# Allows us to prove 
# F = Implies(And(fst(p) == fst(p2), snd(p) == snd(p2)), p == p2)

# Add negation of formula and check
s.add(Not(F))
print(s.check())

