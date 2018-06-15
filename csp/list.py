from init import *
from event import *

# very important function to tackle resursive function
def mk_rec(f,body):
    eq = (f == body)
    vars = f.children()
    q = ForAll(vars, eq)
    qid = ":rec-fun"
    f1 = q.body().arg(0)
    body1 = q.body().arg(1)
    return ForAll(vars, eq, 1, qid, "", patterns=[f1,body1])

##################################################################

List = Datatype('List')
List.declare('cons', ('car',Event),('cdr',List))
List.declare('nil')
List = List.create()

cons = List.cons
car = List.car
cdr = List.cdr
nil = List.nil

csp_solver = default_solver

# list variables
l =  Const('l', List)
l1 = Const('l1', List)
l2 = Const('l2', List)
l3 = Const('l3', List)

x = Const('x', IntSort())

###################################################################################################
# length of a list, e.g., length(<a,a,a>) = 3
#length = Function('length', List, IntSort())
#csp_solver.add( mk_rec(length(l), If(l==nil, 0, 1+length(cdr(l)))) )
###################################################################################################
# concatenation of two lists, e.g., append(<a,b>,<c>) = <a,b,c>
#append = Function('append', List, List, List)
#csp_solver.add( mk_rec(append(l1,l2), If(l1==nil, l2, cons(car(l1), append(cdr(l1),l2)))) )

###########################################################
#check whether a list of is the prefix of the other, e.g., prefix(<a>,<a,b>) is TRUE
prefix = Function('prefix', List, List, BoolSort())
csp_solver.add(mk_rec(prefix(l1,l2), If(l1==nil, True,
                                        If(And(l1!=nil,l2!=nil,car(l1)==car(l2)), prefix(cdr(l1),cdr(l2)), False))))


# the difference of two lists, e.g., t2-t1 or difference(<a,a,b>,<a>,<a,b>) is TRUE
diff = Function('difference', List, List, List, BoolSort())
csp_solver.add(mk_rec(diff(l1,l2,l), If(And(l2==nil,l1==l), True,
                                       If(And(l1!=nil,l2!=nil, car(l1)==car(l2), diff(cdr(l1),cdr(l2), l)), True, False) )))


#s=default_solver

#s.add(diff(cons(a,cons(b,cons(c,nil))), cons(a,nil), l))
#print s.check()
#print s.model()



# a special set for parallelism and hiding, and it uses different ids to identify different sets for different processes
interface = Function('interface', IntSort(), Event, BoolSort())

# parallel composition of two lists
parallel = Function('parallel', IntSort(), List, List, List, BoolSort())

e = Const('e', Event)
id = Int('id')

# definition for parallel
csp_solver.add(mk_rec(parallel(id, l1, l2, l3),
                      If(And(l1 == nil, l2 == nil, l3 == nil), True,
                         If(And(l1 != nil, l2 != nil, l3 != nil, car(l1) == car(l2), car(l1) == car(l3), interface(id,car(l1))),
                            parallel(id, cdr(l1), cdr(l2), cdr(l3)),
                            Or(If(And(l1 != nil, l3 != nil, car(l1) == car(l3), Not(interface(id,car(l1)))),
                                  parallel(id, cdr(l1), l2, cdr(l3)), False),
                               If(And(l2 != nil, l3 != nil, car(l2) == car(l3), Not(interface(id,car(l2)))),
                                  parallel(id, l1, cdr(l2), cdr(l3)), False))))))



#hidingset = Function('hidingset', IntSort(), Channel, BoolSort())
#filter for hiding, <a,a,b>\{a} = <b>
event_filter = Function('event_filter', IntSort(), List, List)
csp_solver.add(mk_rec(event_filter(id,l), If(l==nil, nil,
                                          If(interface(id,car(l)), event_filter(id,cdr(l)), cons(car(l), event_filter(id,cdr(l)))))))

