############################
## Kun Wei 28/06/2018
###########################

from vcsp import *

# y:=x+1 ||| x:=y+1

x,y = Ints('x y')

init = Tuple(True, False, nil, Fullset, LocalTuple(1,1,True), GlobalTuple(1,1))

P = GPar([],GSeq(SP(a),SGAssign(ga, 'gy', 'gx+1')), GSeq(SP(b), SGAssign(gb, 'gx', 'gy+1')))

csp_solver.add(P.relation(P.iv, P.fv), P.iv==init, iv==init, P.fv==fv, ok(fv), Not(wait(fv)), gx(glo(fv))==x, gy(glo(fv))==y)

print (csp_solver.check())
print (csp_solver.model()[x])
print (csp_solver.model()[y])
print (csp_solver.model()[fv])