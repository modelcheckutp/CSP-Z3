######################################
## Kun Wei 28/06/2018
## uncomment to use the examples
#######################################

from vcsp import *

# we've defined two integers, lx and ly, and one boolean variable, lz.

#e1.
# P = lx:=1;ly:=2;lx:=lx+ly
# we expect lx'=3 and ly'=2

#P = Seq(Seq(Assign('lx', '1'), Assign('ly', '2')), Assign('lx', 'ly+lx'))
# this restricts the initial states and some final states
#csp_solver.add(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, ok(fv), Not(wait(P.fv)))
#print(csp_solver.check())
#print(csp_solver.model()[fv])

#e2.
# P = lx:=1 ; (lx>0& a->Skip [] lx<0 & b->Skip)
#P = Seq(Assign('lx', '1'), EC(Guard('lx>0', SP(a)), Guard('lx<0', SP(b))))
#ListAllTraces(P)

