##########################################
#  UTP CSP Theory in Z3py with new recursion feature
#  Kun Wei 08/10/2018
# version 1.0
##########################################

########################################################################################
## model-checking friendly semantics
## R(¬P(f,f) |- P(t,f)) = (R3' R1(P(f,f) or (ok' and P(t,f)))) <| ok |> tr<=tr'
#########################################################################################
## obviously, tr<=tr' is infinite, and hard to be modelled for finite refinement
## when the predecessor diverges, we simply use relational identity
########################################################################################



##########################################
# Assumptions for model checking
# 1. ref' is maximal, e.g., (a not in ref') means ref' is an arbitrary set who does not include a
# 2. ref' is arbitrary when a process terminates, so we use Fullset only to denote it
# 3. tr'<=tr when divergent, but we record tr'=tr only

##########################################
# the new semantic for CSP, not reactive design because it considers wait first
# reactive design: R(not Pff |- Ptf)
# new semantics:  R(Pff or (ok' and Ptf)) <| ok |> tr<=tr'
# in order to simplify model checking, we consider the value of ok first rather than wait in reactive designs.

from list import *
from finite_set import *


#local variable names for integers and bools
# add more datatypes if needed
#LocalIV, (ix,iy,iz) = EnumSort('LocalIntegerVariableName', ('ix','iy','iz'))
#LocalBV, (bx,by,bz) = EnumSort('LocalBoolVariableName', ('bx', 'by', 'bz'))

LocalVar = Datatype('LocalVar')
LocalVar.declare('LocalTuple', ('lx', IntSort()), ('ly', IntSort()), ('lz', BoolSort()))
LocalVar = LocalVar.create()
LocalTuple = LocalVar.LocalTuple
lx = LocalVar.lx
ly = LocalVar.ly
lz = LocalVar.lz

GlobalVar = Datatype('GlobalVar')
GlobalVar.declare('GlobalTuple', ('gx', IntSort()), ('gy', IntSort()))
GlobalVar = GlobalVar.create()
GlobalTuple = GlobalVar.GlobalTuple
gx = GlobalVar.gx
gy = GlobalVar.gy


# local variables as observation
#LocalVariables = Datatype('LocalVariables')
#LocalVariables.declare('SetOfVariableList', ('ia', ArraySort(LocalIV, IntSort())), ('ba', ArraySort(LocalBV, BoolSort())))
#LocalVariables = LocalVariables.create()
#ia = LocalVariables.ia
#ba = LocalVariables.ba

# Observational Variables
Variables = Datatype('Variables')
Variables.declare('Tuple', ('ok', BoolSort()), ('wait', BoolSort()), ('tr', List), ('ref', SetSort),
                           ('loc', LocalVar),  ('glo', GlobalVar))

Variables = Variables.create()

Tuple = Variables.Tuple
ok = Variables.ok
wait = Variables.wait
tr = Variables.tr
ref = Variables.ref
loc = Variables.loc
glo = Variables.glo

iv = Const('iv', Variables)	 # initial variables
fv = Const('fv', Variables)	 # final variables
mv = Const('mv', Variables)	 # temporal variables for composition


# alphabet here is a set of variables whose values will be changed
# the real alphabet for a process will be considered in the future
class Process:
    def __init__(self, predicate, alphabet, expr):
        # each process has a default id which starts from 0
        global global_process_index
        self.id = global_process_index
        global_process_index += 1
        # the expression as string which is useful for sequential composition
        self.expr = expr
        self.iv = Const('iv_%s' % self.id, Variables)
        self.fv = Const('fv_%s' % self.id, Variables)
        #the predicate to match the pair of initial and final
        self.predicate = substitute(predicate, (iv, self.iv), (fv, self.fv))
        #a set of variable names whose values have been changed
        self.alphabet = alphabet
        # a relation of initial and intermediate or final
        self.relation= Function('re_%s'%self.id, Variables, Variables, BoolSort())
        # add the constraint into the engine to implement the matching
        default_solver.add(If(self.predicate, self.relation(self.iv,self.fv), self.relation(self.iv,self.fv)==False))
        #default_solver.check()

#
class PProcess:  # process for parallel because of the alphabetised interface
    def __init__(self, cs, predicate, alphabet, expr):
        # each process has a default id which starts from 0
        global global_process_index
        self.id = global_process_index
        global_process_index += 1

        self.alphabet = alphabet
        self.expr = expr

        self.iv = Const('iv_%s'%self.id, Variables)
        self.fv = Const('fv_%s'%self.id, Variables)
        self.pt3 = Const('pt3_%s'%self.id, List)
        self.pt1 = Const('pt1_%s' % self.id, List)
        self.pt2 = Const('pt2_%s' % self.id, List)

        # the predicate to match the pair of initial and final
        predicate = substitute(predicate, (iv, self.iv), (fv, self.fv),(l3, self.pt3), (l1, self.pt1), (l2, self.pt2) )

        # interface
        al = Set.alphabet # the list of all elements in the alphabet
        for i in range(len(al)):
            if (al[i] in cs):
                default_solver.add(interface(self.id, al[i]))
            else:
                default_solver.add(Not(interface(self.id, al[i])))

        # a relation of initial and intermediate or final
        self.relation = Function('re_%s'%self.id, Variables, Variables, BoolSort())

        # add the constraint into the engine to implement the matching
        default_solver.add(If(predicate, self.relation(self.iv, self.fv), self.relation(self.iv, self.fv) == False))


# conditional: P <| b |> Q
def con(P, b, Q):
    return Or(And(P, b), And(Q, Not(b)))

Identity = (iv == fv)

# IR = ok' and wait'=wait and tr'=tr and ref'=ref and v'=v
IR = And(ok(fv), wait(fv) == wait(iv), tr(fv) == tr(iv), ref(fv) == ref(iv), loc(fv)==loc(iv), glo(fv)==glo(iv))

# for any immediate divergence, we simply allow it to keep the existing observation.
# in order to simplify model checking, we only keep the previous value for ref
# of course, we can further reduce the space by limiting the values for other variables
IDiv = And(tr(iv) == tr(fv), ref(fv) == Fullset)

############################################
# selective healthiness conditions
############################################
# R1(P) = P and tr<=tr'
def R1(P):
    return And(P, prefix(tr(iv), tr(fv)))


# R3(P) = IdentityR <| wait |> P
# IR is just a right part of the original definition because of the new style of the semantics
def R3(P):
    return con(IR, wait(iv), P)

def R(P):
    return R3(P)
    #return R3(R1(P))

############################################
# primitive processes
############################################

# Chaos = R(true), but we set ok' false to get a simple model
# Chaos = R(True) <| ok |> tr<=tr')
# FDR splits Chaos into two processes, IDiv and RUN. IDiv diverges immediately,
# and RUN can execute any possible traces. We keep the idea of IDiv only but also
# retain RUN by means of refinement. Anyway, the Z3 semantics of Chaos as
# Chaos = R(IDiv) <| ok |> IDiv
Chaos = Process(con(R(IDiv), ok(iv), IDiv), set(), "Chaos")

# Miracle = R(not ok)
# Miracle = R(false) |> ok <| IDiv
Miracle = Process(con(R(False), ok(iv), IDiv), set(), "Miracle")

# Stop = R(wait:=true)
# Stop = R(true |- tr'=tr and wait')
# Stop = R(ok' and tr'=tr and wait' and ref'=FullSet) <| ok |> IDiv
Stop = Process(con(R(And(ok(fv), wait(fv), tr(fv) == tr(iv), ref(fv) == Fullset)), ok(iv), IDiv), set(), "Stop")

# Skip = R(true |- tr'=tr and not wait')
# Skip = R(ok' and tr'=tr and not wait and ref'=FullSet <| ok |> IDiv)
Skip = Process(con(R(And(ok(fv), Not(wait(fv)), tr(fv) == tr(iv), loc(iv)==loc(fv), glo(iv)==glo(fv),ref(fv) == Fullset)),
                   ok(iv), IDiv), set(), "Skip")


###################################################################
# Simple Prefix, e.g., a->Skip
###################################################################
# SP(a) = R(true |- tr'=tr and a noin ref' <| wait' | tr'=tr+<a>)
# SP(a) = R(ok' and tr'=tr and a notin ref') <| wait' |> tr'=tr+<a>)

## transfrom a copound event into a string
def EventToString(e):
    if e.num_args()==0:
        return e.decl().name()
    else:
        #remove the first bracket
        s = e.sexpr().replace("(", "", 1)
        #add a bracket after CE
        s = s.replace(" ", "(", 1)
        #replace all whitespaces into semi-coma
        s = s.replace(" ", ",")
        return s


def SP(a):
    max_ref = Set.complement(Set.add(a,Set.emptyset()))
    return Process(con(R(And(ok(fv), con(And(tr(fv)==tr(iv), ref(fv)==max_ref),
                                             wait(fv),
                                             And(diff(tr(fv),tr(iv),cons(a,nil)), loc(fv)==loc(iv), glo(fv)==glo(iv), ref(fv)==Fullset)))),
                       ok(iv),
                       IDiv), set(), "SP("+EventToString(a)+")")

####################################################################################
# sequential composition
####################################################################################
# P;Q = R(¬(R1(Pff);R1(true)) and ¬(R1(Ptf);R1(¬wait and QFF))
#                              |-
#         R1(Ptf);R1(II <|wait' |> Qtf)
####################################################################################
# simplfied Z3 semantics
# P;Q = R(Pff or Ptf;Qff or (ok' and (Ptf <| wait'|>Qtf))) <| ok |> IDiv
def Seq(P, Q):
    nsp = eval(Q.expr)  #nsp is a brand-new process
    return Process(con(R(Or(And(P.relation(P.iv, P.fv), P.iv==iv, P.fv==fv, Not(ok(fv))),  # P diverges
                            And(P.relation(P.iv, P.fv), nsp.relation(nsp.iv, nsp.fv), P.iv==iv, nsp.fv==fv,
                                nsp.iv==P.fv, ok(P.fv), Not(wait(P.fv)), Not(ok(fv))),     # Q is divergent, P is not
                            And(P.relation(P.iv, P.fv), P.iv==iv, P.fv==fv, ok(fv), wait(fv)),  # P is waiting
                            And(P.relation(P.iv, P.fv), nsp.relation(nsp.iv, nsp.fv), P.iv==iv, nsp.fv==fv,
                                nsp.iv==P.fv, ok(P.fv), Not(wait(P.fv)), ok(fv)))),
                       ok(iv), IDiv), set.union(P.alphabet, Q.alphabet), "Seq(" + P.expr + "," + Q.expr + ")")



#################################################################
### assignment
#################################################################

def LocalVariableNamesToString(V):
    ls = [];
    for i in range(V.constructor(0).arity()):
        ls.append(V.accessor(0,i).name())
    return ls

#print(LocalVariablesToString(LocalVar))
#print (substitute(lx+1, (lx, ly(loc(iv)))))

#print(lx(loc(iv)))

def ReplaceVariablesByValuesWithoutGlobal(expr):
    localnames = LocalVariableNamesToString(LocalVar)
    for i in range(len(localnames)):
        expr = expr.replace(localnames[i], localnames[i]+'(loc(iv))')
    return expr

def ReplaceVariablesByValues(expr):
    localnames = LocalVariableNamesToString(LocalVar)
    globalnames = LocalVariableNamesToString(GlobalVar)
    for i in range(len(localnames)):
        expr = expr.replace(localnames[i], localnames[i]+'(loc(iv))')
    for i in range(len(globalnames)):
        expr = expr.replace(globalnames[i], globalnames[i] + '(glo(iv))')
    return expr

def AssignmentConstraints(v, expr):
    localnames = LocalVariableNamesToString(LocalVar)
    globalnames = LocalVariableNamesToString(GlobalVar)

    # replace all variables in the left with iv
    for i in range(len(localnames)):
        expr = expr.replace(localnames[i], localnames[i] + '(loc(iv))')
    for i in range(len(globalnames)):
        expr = expr.replace(globalnames[i], globalnames[i] + '(glo(iv))')
    # produce the full constraints for assignment
    constraints = ''
    for i in range(len(localnames)):
        if localnames[i] != v:
            constraints = constraints + ',' + localnames[i] + '(loc(fv))==' + localnames[i] + '(loc(iv))'
    for i in range(len(globalnames)):
        if globalnames[i] != v:
            constraints = constraints + ',' + globalnames[i] + '(glo(fv))==' + globalnames[i] + '(glo(iv))'
    if v in localnames:
        return 'And(' + v + '(loc(fv))==' + expr + ',' + constraints[1:] + ')'
    else:
        return 'And(' + v + '(glo(fv))==' + expr + ',' + constraints[1:] + ')'

#print(AssignmentConstraints('gx', 'gx+lx'))




def AssignmentConstraintsWithoutGlobal(v, expr):
    localnames = LocalVariableNamesToString(LocalVar)

    # replace all variables in the left with iv
    for i in range(len(localnames)):
        expr = expr.replace(localnames[i], localnames[i] + '(loc(iv))')

    # produce the full constraints for assignment
    constraints = ''
    for i in range(len(localnames)):
        if localnames[i] != v:
            constraints = constraints + ',' + localnames[i] + '(loc(fv))==' + localnames[i] + '(loc(iv))'

    return 'And(' + v + '(loc(fv))==' + expr + ',' + constraints[1:] + ')'


# assignment: v and expr must be Strings. For example, lx:=lx+1 should be Assign('lx', 'lx+1')
# expr must be a string which contains undashed only
def Assign(v, expr):
    return Process(con(R(And(ok(fv), Not(wait(fv)), tr(fv) == tr(iv), ref(fv) == Fullset, eval(AssignmentConstraints(v,expr)))),
                       ok(iv), IDiv), set([v]), "Assign('"+ v +"','"+expr+"')")


#expr must be a string containing undashed variables
def Guard(expr, P):
    return Process(con(R(con(And(P.relation(P.iv,P.fv), P.iv==iv, P.fv==fv),
                                 eval(ReplaceVariablesByValues(expr)),
                                 And(ok(fv), wait(fv), tr(fv)==tr(iv), ref(fv)==Fullset))),
                       ok(iv), IDiv), P.alphabet, "Guard('" + expr +"'," + P.expr +")")

#x = Int('x')
#y = Int('y')
#init = Tuple(True, False, nil, Fullset, LocalTuple(0,0,True), GlobalTuple(0,0))
#P = Seq(Assign('lx', '1'), Guard('lx>0', Skip))
#csp_solver.add(P.relation(P.iv, P.fv), P.iv==init, P.fv==fv, ok(fv), Not(wait(fv)), lx(loc(fv))==x)
#print(csp_solver.check())
#print(csp_solver.model()[x])


# external choince
# P[]Q = R(¬Pff and ¬Qff |- (Ptf and Qtf) <| tr'=tr and wait' |> (Ptf or Qtf))
# P[]Q = R(Pff or Qff or (ok' and (Ptf and Qtf <| tr'=tr and wait' |> Ptf or Qtf))) <| ok |> IDiv
def EC(P, Q):
    return Process(con(R(Or(And(P.relation(P.iv, P.fv), P.iv == iv, P.fv == fv, Not(ok(fv))),  # Pff
                            And(Q.relation(Q.iv, Q.fv), Q.iv == iv, Q.fv == fv, Not(ok(fv))),  # Qff
                            And(ok(fv), con(And(P.relation(P.iv, P.fv), Q.relation(Q.iv, Q.fv), P.iv == iv, Q.iv == iv,
                                                ok(P.fv), wait(P.fv), tr(P.iv) == tr(P.fv), ok(Q.fv), wait(Q.fv),
                                                tr(Q.iv) == tr(Q.fv), ref(fv) == Set.intersection(ref(P.fv), ref(Q.fv))),
                                            And(tr(iv) == tr(fv), wait(fv)),
                                            Or(And(P.relation(P.iv, P.fv), P.iv == iv, P.fv == fv),
                                               And(Q.relation(Q.iv, Q.fv), Q.iv == iv, Q.fv == fv)))))),
                       ok(iv), IDiv), set().union(P.alphabet, Q.alphabet), "EC(" + P.expr + "," + Q.expr + ")")

# internal choice
# P |~| Q = R(¬Pff and ¬Qff |- Ptf or Qtf)
# P|~|Q = R(Pff or Qff or (ok' and (Ptf or Qtf))) <| ok |> IDiv
def IC(P, Q):
    return Process(con(R(Or(And(P.relation(P.iv, P.fv), P.iv == iv, P.fv == fv, Not(ok(fv))),
                            And(Q.relation(Q.iv, Q.fv), Q.iv == iv, Q.fv == fv, Not(ok(fv))),
                            And(P.relation(P.iv, P.fv), P.iv == iv, P.fv == fv, ok(fv)),
                            And(Q.relation(Q.iv, Q.fv), Q.iv == iv, Q.fv == fv, ok(fv)))),
                       ok(iv), IDiv), set().union(P.alphabet, Q.alphabet), "IC(" + P.expr + "," + Q.expr + ")")

### Parallel Composition
### P [| A |] Q = (ok'== P.ok' and Q.ok') and (wait'== P.wait' or Q.wait') and (tr'-tr==prod(A,P.tr'-P.tr,Q.tr'-Q.tr))
###                ref' = union(inter(union(P.ref',Q.ref'),A), (inter(P.ref',Q.ref')\A)
# s is a set of variables which need updating
# left and right are arrays of variables for integers, bool or other
# ll is a list of variable names for certain type
def UpdateLocalValuesToString(s, left, right, ll):
    c=left
    for e in s:
        if e in ll:
            c = Store(c, eval(e), Select(right,eval(e)))
    return c

def AllVariableUpdateInParallel(s1, s2): # s1 is for P and s2 is for Q by default
    assert(s1.intersection(s2)== set())
    localnames = LocalVariableNamesToString(LocalVar)
    globalnames = LocalVariableNamesToString(GlobalVar)

    expr = ''
    for i in s1:
        if i in localnames:
            expr = expr + ',' + i + '(loc(P.fv))==' + i + '(loc(fv))'
        if i in globalnames:
            expr = expr + ',' + i + '(glo(P.fv))==' + i + '(glo(fv))'
    for i in s2:
        if i in localnames:
            expr = expr + ',' + i + '(loc(Q.fv))==' + i + '(loc(fv))'
        if i in globalnames:
            expr = expr + ',' + i + '(glo(Q.fv))==' + i + '(glo(fv))'

    s3 = s1.union(s2)
    for i in localnames:
        if i not in s3:
            expr = expr + ',' + i + '(loc(fv))==' + i + '(loc(iv))'
    for i in globalnames:
        if i not in s3:
            expr = expr + ',' + i + '(glo(fv))==' + i + '(glo(iv))'

    return 'And(' + expr[1:] + ')'

def LocalVariableUpdateInParallel(s1, s2): # s1 is for P and s2 is for Q by default
    assert(s1.intersection(s2)== set())
    localnames = LocalVariableNamesToString(LocalVar)

    expr = ''
    for i in s1:
        if i in localnames:
            expr = expr + ',' + i + '(loc(P.fv))==' + i + '(loc(fv))'

    for i in s2:
        if i in localnames:
            expr = expr + ',' + i + '(loc(Q.fv))==' + i + '(loc(fv))'
    s3 = s1.union(s2)
    for i in localnames:
        if i not in s3:
            expr = expr + ',' + i + '(loc(fv))==' + i + '(loc(iv))'
    return 'And(' + expr[1:] + ')'

#print(LocalVariableUpdateInParallel(set(['lx','ly']), set(['lz','gy'])))

def Par(CS, P, Q):
    r = Set.toSet(CS)  # r is  the interface
    return PProcess(CS, con(R(And(P.relation(P.iv, P.fv), Q.relation(Q.iv, Q.fv), P.iv == iv, Q.iv == iv,
                                  ok(fv) == And(ok(P.fv), ok(Q.fv)), wait(fv) == Or(wait(P.fv), wait(Q.fv)),
                                  diff(tr(P.fv), tr(iv), l1), diff(tr(Q.fv), tr(iv), l2), diff(tr(fv), tr(iv), l3),
                                  parallel(global_process_index, l1, l2, l3),
                                  ref(fv) == (Set.union(Set.intersection(Set.union(ref(P.fv), ref(Q.fv)), r),
                                                        Set.difference(Set.intersection(ref(P.fv), ref(Q.fv)),r))),
                                  eval(AllVariableUpdateInParallel(P.alphabet, Q.alphabet)))),
                            ok(iv), IDiv), set().union(P.alphabet, Q.alphabet), "Par(" + str(CS) + "," + P.expr + "," + Q.expr + ")")

###################################
# testing for parallel
###################################
#x = Int('x')
#y = Int('y')
#print (csp_solver.model()[x])
#print (csp_solver.model()[y])
#print (s.model()[fv])

### Hiding
#def Hide(P, CS):
#    r = Set.toSet(CS)
#    return PProcess(CS, con(R(And(P.relation(P.iv, P.fv), P.iv == iv,
#                                  diff(tr(P.fv), tr(P.iv), l1),
#                                  diff(tr(fv), tr(P.iv), l), event_filter(global_process_index, l1) == l,
#                                  ref(fv) == Set.union(ref(P.fv), r), ref(P.fv) == Set.union(ref(fv), r),
#                                  ok(P.fv) == ok(fv), wait(P.fv) == wait(fv), loc(P.fv)==loc(fv))),
#                            ok(iv), IDiv), P.alphabet, "Hide(" + P.expr + "," + str(CS) + ")")



#######################################
### operators with shared variables
#######################################

#GSeq(P,Q) for linking processes with shared variables, because Q won't take initial values for shared variables

def GSeq(P, Q):
    nsp = eval(Q.expr)  #nsp is a brand-new process
    return Process(con(R(Or(And(P.relation(P.iv, P.fv), P.iv==iv, P.fv==fv, Not(ok(fv))),  # P diverges
                            And(P.relation(P.iv, P.fv), nsp.relation(nsp.iv, nsp.fv), P.iv==iv, nsp.fv==fv,
                                ok(nsp.iv)==ok(P.fv), wait(nsp.iv)==wait(P.fv),tr(nsp.iv)==tr(P.fv),
                                ref(nsp.iv)==ref(P.fv), loc(nsp.iv)==loc(P.fv),
                                ok(P.fv), Not(wait(P.fv)), Not(ok(fv))),     # Q is divergent, P is not
                            And(P.relation(P.iv, P.fv), P.iv==iv, P.fv==fv, ok(fv), wait(fv)),  # P is waiting
                            And(P.relation(P.iv, P.fv), nsp.relation(nsp.iv, nsp.fv), P.iv==iv, nsp.fv==fv,
                                ok(nsp.iv) == ok(P.fv), wait(nsp.iv) == wait(P.fv), tr(nsp.iv) == tr(P.fv),
                                ref(nsp.iv) == ref(P.fv), loc(nsp.iv) == loc(P.fv),
                                ok(P.fv), Not(wait(P.fv)), ok(fv)))),
                       ok(iv), IDiv), set.union(P.alphabet, Q.alphabet), "GSeq(" + P.expr + "," + Q.expr + ")")

# attachin for linking signature events with input
# attachout for linking signature events with output
attachin = Function('attachin',   Event, GlobalVar)
attachout = Function('attachout', Event, GlobalVar)


def GAssign(a, v, expr):
    return Process(con(R(And(ok(fv), Not(wait(fv)), tr(fv) == tr(iv), ref(fv) == Fullset,
                             attachin(a) == glo(iv), attachout(a) == glo(fv), eval(AssignmentConstraints(v,expr)))),
                       ok(iv), IDiv), set(), "GAssign("+ EventToString(a)+ ",'" + v +"','"+expr+"')")

#in case GAssign is the beginning of a process
def SGAssign(a,v,expr):
    return GSeq(SP(a), GAssign(a, v, expr))




#b&Skip

def GuardSkip(a, expr):
    return Process(con(R(con(And(ok(fv), Not(wait(fv)), tr(fv) == tr(iv), loc(iv)==loc(fv), glo(iv)==glo(fv),
                                 ref(fv) == Fullset, attachin(a)==glo(iv), attachout(a)==glo(fv)),
                             eval(ReplaceVariablesByValues(expr)),
                             And(ok(fv), wait(fv), tr(fv)==tr(iv), ref(fv)==Fullset))),
                       ok(iv), IDiv), set(), "GuardSkip(" + EventToString(a)+ ",'" + expr + "')")

def GGuard(a, expr, P):
    return Seq(GSeq(SP(a), GuardSkip(a,expr)), P)


# the recursive funcntion chain create a chain for value passing for shared variables via the given trace
chain = Function('chain', List, BoolSort())
csp_solver.add(mk_rec(chain(l), If(l == nil, True,
                                   If(cdr(l) == nil, attachout(car(l))==glo(fv),
                                      And(attachout(car(l)) == attachin(car(cdr(l))), chain(cdr(l)))))))
#set the init for shared variables
def fullchain(l):
    return If(l==nil, True, And(glo(iv)==attachin(car(l)), chain(l)))


#x,y = Ints('x y')
#init = Tuple(True, False, nil, Fullset, LocalTuple(1,1,True), GlobalTuple(1,1))
#P = SGAssign(ga, 'gy', 'gx+1')
#csp_solver.add(P.relation(P.iv, P.fv), P.iv==init, iv==init, P.fv==fv, ok(fv), Not(wait(fv)), gx(glo(fv))==x, gy(glo(fv))==y)
#csp_solver.add(chain(cons(ga,nil)))
#csp_solver.add(fullchain(cons(ga,nil)))
#print (csp_solver.check())
#print (csp_solver.model()[y])
#print (csp_solver.model()[x])

#x,y = Ints('x y')
#init = Tuple(True, False, nil, Fullset, LocalTuple(1,1,True), GlobalTuple(1,1))
#P = Seq(Assign('gx', 'gx+lx'), Assign('gy', 'gx+1'))
#csp_solver.add(P.relation(P.iv, P.fv), P.iv==init, P.fv==fv, ok(fv), Not(wait(fv)), lx(loc(fv))==x, gy(glo(fv))==y)
#csp_solver.add(chain(cons(ga,cons(gb,nil))))
#print (csp_solver.check())
#print (csp_solver.model()[y])
#print (csp_solver.model()[fv])


def seinterface():
    al = Set.alphabet  # the list of all elements in the alphabet
    for i in range(len(al)):
        if (al[i] in SE):
            default_solver.add(signatures(al[i]))
        else:
            default_solver.add(Not(signatures(al[i])))



def GPar(CS, P, Q):
    r = Set.toSet(CS)  # r is  the interface999
    seinterface() # build a constraints for signature interface
    return PProcess(CS, con(R(And(P.relation(P.iv, P.fv), Q.relation(Q.iv, Q.fv), P.iv == iv, Q.iv == iv,
                                  ok(fv) == And(ok(P.fv), ok(Q.fv)), wait(fv) == Or(wait(P.fv), wait(Q.fv)),
                                  diff(tr(P.fv), tr(iv), l1), diff(tr(Q.fv), tr(iv), l2), diff(tr(fv), tr(iv), l3),
                                  parallel(global_process_index, l1, l2, l3),
                                  event_projection(global_process_index,l3) ==l, fullchain(l),
                                  ref(fv) == (Set.union(Set.intersection(Set.union(ref(P.fv), ref(Q.fv)), r),
                                                        Set.difference(Set.intersection(ref(P.fv), ref(Q.fv)),r))),
                                  eval(LocalVariableUpdateInParallel(P.alphabet, Q.alphabet))
                                  )),
                            ok(iv), IDiv), set().union(P.alphabet, Q.alphabet), "GPar(" + str(CS) + "," + P.expr + "," + Q.expr + ")")











############################################
## not check refinement yet
############################################



################################################################
## Functions to enumerate all possible traces and refusal sets
################################################################
#init = Tuple(True, False, nil, Fullset)
# ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset

# show one trace for termination
def ListOneTerminatedTrace(P):
    s = default_solver
    s.push()
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, ok(fv), Not(wait(fv))))
    if s.check()!=unsat:
        print (s.model()[fv].children()[2])
    else:
        print ("No solution!")
    s.pop()

# show all terminated traces
def ListAllTerminatedTraces(P):
    s = default_solver
    s.push()
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, ok(fv), Not(wait(fv))))

    while s.check() != unsat:
        m = s.model()
        t = m[fv].children()[2]
        print (t)
        s.add(tr(fv) != t)
    s.pop()
    print ("Done")

# show all traces which are deadlock or terminated
def ListAllTraces(P):
    s = default_solver
    s.push()
    s.add( And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv==fv))
    #stable
    s.push()
    s.add(ok(fv))
    print ("Stable:")

    while s.check() != unsat:
        m = s.model()
        #print (m)
        t= (m[fv].children()[2])
        print (t)
        s.add( tr(fv) != t )

    s.pop()
    # divergent
    s.add(Not(ok(fv)))

    print("Divergent:")
    while s.check() == sat:
        m = s.model()
        t = m[fv].children()[2]
        print (t)
        s.add(tr(fv) != t)
    s.pop()
    print("Done")

# show all traces and their refusals including divergent traces
def ListAllTracesAndRefs(P):
    s = default_solver
    s.push()

    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv))
    # stable
    s.push()
    s.add(ok(fv))
    print ("Stable:")
    while s.check() != unsat:
        m = s.model()
        t = m[fv].children()[2]
        r = m[fv].children()[3]
        print (t, Set.toElements(r))

        s.push()
        s.add(And(tr(fv)==t, ref(fv)!=r))
        while s.check() == sat:
            m1 = s.model()
            t1 = m1[fv].children()[2]
            r1 = m1[fv].children()[3]
            print (t1, Set.toElements(r1))
            s.add(ref(fv)!=r1)
        s.pop()

        s.add(tr(fv)!=t)
    s.pop()

    # divergent
    s.add(Not(ok(fv)))
    print("Divergent:")
    while s.check() == sat:
        m = s.model()
        t = m[fv].children()[2]
        print (t)
        s.add(tr(fv) != t)

    s.pop()
    print("Done")


##########################################################
#### Refinement ##########################################
#### P refines Q iff P => Q ##############################
#### TRef : check traces only
#### SFRef: check traces and refusals
#### DFRef: check failures and divergences
##########################################################

# check stable traces only; that is ok' is true and ignore any divergent trace.
# ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset
# ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset
def TRef(P,Q):
    s = default_solver
    s.push() #1
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, ok(fv)))

    while s.check() !=unsat:
        m = s.model()
        t = m[fv].children()[2]
        print (t)

        s.push() #2 for Q
        s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, ok(Q.fv), tr(Q.fv)==t))
        if s.check()==sat:
            s.pop() #2
        else:
            print ("No refinement")
            s.pop() #2
            s.pop() #1
            return
        s.add(tr(fv) != t)

    s.pop() #1
    print ("Refined!!!")

# check stable traces and refusals
def SFRef(P,Q):
    s = default_solver
    s.push() #1
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, ok(fv)))

    while s.check() != unsat:
        m = s.model()
        t = m[fv].children()[2]
        r = m[fv].children()[3]
        print (t, Set.toElements(r))
        #checking Q
        s.push() #2
        s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, ok(Q.fv), tr(Q.fv) == t, ref(Q.fv)==r))
        if s.check() == sat:
            s.pop() #2 remove the constraint for Q
            # same trace but different refusals
            s.push() #3 for P, same trace but different refs
            s.add(And(tr(fv)==t, ref(fv)!=r))
            while s.check() == sat:
                m1 = s.model()
                #t1 = m[fv].children()[2]
                r1 = m1[fv].children()[3]
                print (t, Set.toElements(r1))
                #checning Q
                s.push() #4 constraint for Q again
                s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, ok(Q.fv), tr(Q.fv) == t, ref(Q.fv) == r1))
                if s.check() == sat:
                    s.pop() #4
                    s.add(ref(fv)!=r1) # add into 3
                else:
                    s.pop() #4
                    s.pop() #3
                    s.pop() #1
                    print ("No refinement")
                    return
            s.pop() #3 remove all constraints about this trace(P)
            s.add(tr(fv)!=t) # add into 1
        else:
            print ("No refinement")
            s.pop() #2
            s.pop() #1
            return
    s.pop() # remove 1
    print ("Refined!!!")

# refusla set

#################################################################################
# the procedure for Divergence-Failure is very complex because we record
# the least observation for divergence rather than arbitrary Obs
# So, we check non-divergent and divergent behaviours separately
##################################################################################

###############################################
## auxiliary function for divergent checking
###############################################

def isDivergent(P):
    s = default_solver
    s.push()
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, Not(ok(fv))))
    if s.check() != unsat:
        s.pop()
        return True
    else:
        s.pop()
        return False

# P is non-divergent and Q is divergent
def NonDivergentRefineDivergent(P,Q):
    s = default_solver
    s.push()  # 1
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, ok(fv)))

    while s.check() != unsat:
        m = s.model()
        t = m[fv].children()[2]
        r = m[fv].children()[3]
        print(t, Set.toElements(r))
        # checking Q
        s.push()  # 2
        s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, ok(Q.fv), tr(Q.fv) == t, ref(Q.fv) == r))
        if s.check() == sat: # whether the trace is included in Q
            s.pop()  # 2 remove the constraint for Q
            # same trace but different refusals
            s.push()  # 3 for P, same trace but different refs
            s.add(And(tr(fv) == t, ref(fv) != r))
            while s.check() == sat:
                m1 = s.model()
                # t1 = m[fv].children()[2]
                r1 = m1[fv].children()[3]
                print(t, Set.toElements(r1))
                # checning Q
                s.push()  # 4 constraint for Q again
                s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, ok(Q.fv), tr(Q.fv) == t, ref(Q.fv) == r1))
                if s.check() == sat:
                    s.pop()  # 4
                    s.add(ref(fv) != r1)  # add into 3
                else:
                    s.pop()  # 4

                    s.push()  # check divergent trace
                    s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, Not(ok(Q.fv)), prefix(tr(Q.fv), t)))
                    if s.check() == unsat:
                        s.pop() # pop up the constraint for divergence
                        s.pop() #3
                        s.pop() #1
                        print ("No refinement")
                        return
                    else:
                        s.pop() # pop up divergence
                        s.add(ref(fv) != r1)  # add into 3

            s.pop()  # 3 remove all constraints about this trace(P)
            s.add(tr(fv) != t)  # add into 1
        else:
            s.pop()  # 2 remove the constraint for Q and add in new one for divergence
            s.push() # check divergent trace
            s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, Not(ok(Q.fv)), prefix(tr(Q.fv),t)))
            if s.check()==unsat:
                s.pop()
                print ("No refinement!!!")
                s.pop()  # 1
                return # exit the first while loop
            s.pop()
            s.add(And(tr(fv) != t))
    s.pop()  # remove 1
    print("Refined!!!")

def DivergentRefineDivergent(P,Q):
    s = default_solver
    s.push()  # 1
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, ok(fv)))

    while s.check() != unsat:
        m = s.model()
        t = m[fv].children()[2]
        r = m[fv].children()[3]
        print(t, Set.toElements(r))
        # checking Q
        s.push()  # 2
        s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, ok(Q.fv), tr(Q.fv) == t, ref(Q.fv) == r))
        if s.check() == sat:  # whether the trace is included in Q
            s.pop()  # 2 remove the constraint for Q
            # same trace but different refusals
            s.push()  # 3 for P, same trace but different refs
            s.add(And(tr(fv) == t, ref(fv) != r))
            while s.check() == sat:
                m1 = s.model()
                # t1 = m[fv].children()[2]
                r1 = m1[fv].children()[3]
                print(t, Set.toElements(r1))
                # checning Q
                s.push()  # 4 constraint for Q again
                s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, ok(Q.fv), tr(Q.fv) == t, ref(Q.fv) == r1))
                if s.check() == sat:
                    s.pop()  # 4
                    s.add(ref(fv) != r1)  # add into 3
                else:
                    s.pop()  # 4

                    s.push()  # check divergent trace
                    s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, Not(ok(Q.fv)), prefix(tr(Q.fv), t)))
                    if s.check() == unsat:
                        s.pop()  # pop up the constraint for divergence
                        s.pop()  # 3
                        s.pop()  # 1
                        print("No refinement")
                        return
                    else:
                        s.pop()  # pop up divergence
                        s.add(ref(fv) != r1)  # add into 3

            s.pop()  # 3 remove all constraints about this trace(P)
            s.add(tr(fv) != t)  # add into 1
        else:
            s.pop()  # 2 remove the constraint for Q and add in new one for divergence
            s.push()  # check divergent trace
            s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, Not(ok(Q.fv)), prefix(tr(Q.fv), t)))
            if s.check() == unsat:
                s.pop()
                print("No refinement!!!")
                s.pop()  # 1
                return  # exit the first while loop
            s.pop()

            s.add(tr(fv) != t)

    s.pop()  # remove 1


    ###################
    # check divergence
    s.push() #0
    s.push() #1
    s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, Not(ok(fv))))

    while s.check() != unsat:
        m = s.model()
        t = m[fv].children()[2]
        print(t, "Divergent")

        s.pop() #1

        s.push() #2
        s.add(And(Q.relation(Q.iv, Q.fv), ok(Q.iv)==True, wait(Q.iv)==False, tr(Q.iv)==nil, ref(Q.iv)==Fullset, Not(ok(Q.fv)), prefix(tr(Q.fv),t)))
        if s.check()!= unsat:
            s.pop() #2
            s.add(And(tr(fv) != t))
            s.push() #1
            s.add(And(P.relation(P.iv, P.fv), ok(P.iv)==True, wait(P.iv)==False, tr(P.iv)==nil, ref(P.iv)==Fullset, P.fv == fv, Not(ok(fv))))
        else:
            s.pop() #2
            s.pop() #0
            print ("No Refinement!!!")
            return
    s.pop()
    s.pop()
    print ("refined!!!")

# failure-divergence model
def FDRef(P,Q):

    DoP = isDivergent(P)
    DoQ = isDivergent(Q)
    # P and Q are non-divergent, so use SFRef for refinement
    if DoP==False and DoQ==False:
        SFRef(P,Q)
    # If P is divergent and Q is not, then P cannot refine Q
    elif DoP==True and DoQ==False: #
        print ("No refinement")
    elif DoP==False and DoQ==True:
        NonDivergentRefineDivergent(P,Q)
    else:
        DivergentRefineDivergent(P,Q)

