from z3 import *
a, b, res = Bools('a b res')

s = Solver()

# precondition implies wp

wp = Or(
       And(
         a,
         Or(
           And(
             b,
             True == Implies(a, b)
           ), 
           And(
             Not(b),
             False == Implies(a, b)
           )
         )
       ),
       And(
         Not(a),
         True == Implies(a, b)
       )
     )

PO = Implies(True, wp)

# check validity
s.add(Not(PO))

print( s.check() )

