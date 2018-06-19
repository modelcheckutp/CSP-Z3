from vcsp import *

s = String('s')
s2 = String('s2')

f = Function('f', Event, StringSort())

csp_solver.add(f(a)==StringVal("abc"))
csp_solver.add(f(b)==StringVal("def"))
csp_solver.add(f(c)==StringVal("h"))
csp_solver.add(f(d)==StringVal("i"))

shuttle = Function('shuttle', List, StringSort())
csp_solver.add(mk_rec(shuttle(l), If(l== nil, StringVal("skip"+"skip"), Concat(f(car(l)), shuttle(cdr(l))))))

csp_solver.add(shuttle(cons(c,cons(a,cons(b,nil)))) == s2 )

print(csp_solver.check())
print(csp_solver.model()[s2])