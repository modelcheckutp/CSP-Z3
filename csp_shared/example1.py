from vcsp import *

########################################
## gx=0&gx:=gx+1 ||| gx=1&a->Skip
########################################

x = Int('x')
y = Int('y')
init = Tuple(True, False, nil, Fullset, LocalTuple(0,0,True), GlobalTuple(0,0))

P = GPar([], GGuard(ga, 'gx==0', SGAssign(gb, 'gx', 'gx+1')), GGuard(gc, 'gx==1', SP(a)))

csp_solver.add(P.relation(P.iv, P.fv), P.iv==init, init==iv, P.fv==fv, ok(fv), Not(wait(fv)))

print(csp_solver.check())
print(csp_solver.model()[fv])