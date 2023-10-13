from z3 import *

a, b, c = Reals('a b c')

d = b*b - 4*a*c

wp = Or(
         And(d < 0, False),
         And(
           Not(d < 0),
           a*((-b + Sqrt(d))/2)*((-b + Sqrt(d))/2) + b*((-b + Sqrt(d))/2) + c == 0
         )
       )

PO = Implies(
       And(a == 1, 0 <= b*b - 4*c),
       wp
     )


# check validity
s = Solver()
s.add(Not(PO))
print( s.check() )

