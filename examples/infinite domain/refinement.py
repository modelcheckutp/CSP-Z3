from z3 import *

from list import *

x = Const('x', Channel)

csp_solver.add(ForAll(x, prefix(cons(CE(input,x),nil), cons(CE(input,x), cons(CE(output,x),nil)))))
print(csp_solver.check())
#print(csp_solver.model())
