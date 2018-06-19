##########################################
#  Special CSP version for dining philosophers problem
#  Kun Wei 25/04/2018
##########################################

from list import *
from finite_set import *


# Observational Variables
Variables = Datatype('Variables')
Variables.declare('Tuple', ('ok', BoolSort()), ('wait', BoolSort()), ('tr', List), ('ref', SetSort))
Variables = Variables.create()

Tuple = Variables.Tuple
ok = Variables.ok
wait = Variables.wait
tr = Variables.tr
ref = Variables.ref

iv = Const('iv', Variables)	 # initial variables
fv = Const('fv', Variables)	 # final variables
mv = Const('mv', Variables)	 # temporal variables for composition


# each process is an object of the process class
# we have two classess for sequential processes and synchronised processes
# definition for sequential processes
class Process:
    def __init__(self, predicate, expr):
        # each process has a default id which starts from 0
        global global_process_index
        self.id = global_process_index
        global_process_index += 1

        self.expr = expr

        self.iv = Const('iv_%s' % self.id, Variables)
        self.fv = Const('fv_%s' % self.id, Variables)

        #the predicate to match the pair of initial and final
        predicate = substitute(predicate, (iv, self.iv), (fv, self.fv))

        # a relation of initial and intermediate or final
        self.relation= Function('re_%s'%self.id, Variables, Variables, BoolSort())

        # add the constraint into the engine to implement the matching
        default_solver.add(If(predicate, self.relation(self.iv,self.fv), self.relation(self.iv,self.fv)==False))


# process for parallel because of the alphabetised interface
class PProcess:
    def __init__(self, cs, predicate, expr):
        # each process has a default id which starts from 0
        global global_process_index
        self.id = global_process_index
        global_process_index += 1

        self.expr = expr

        self.iv = Const('iv_%s'%self.id, Variables)
        self.fv = Const('fv_%s'%self.id, Variables)
        self.pt1 = Const('pt1_%s'%self.id, List)    # pt1 for P
        self.pt2 = Const('pt2_%s' % self.id, List) # pt2 for Q
        self.pt3 = Const('pt3_%s' % self.id, List) # pt3 for P||Q

        # the predicate to match the pair of initial and final
        predicate = substitute(predicate, (iv, self.iv), (fv, self.fv),(l1, self.pt1), (l2, self.pt2), (l3, self.pt3) )
        #print(predicate)
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

# relational identity: no change
Identity = (iv == fv)

# we record <> only if a process diverges immediately
# and keep ref' is fullset for simplicity
IDiv = And(tr(iv) == tr(fv), ref(fv)==Fullset)

# reactive identity for ok' only
# IR = ok' and wait'=wait and tr'=tr and ref'=ref
IR = And(ok(fv), wait(fv) == wait(iv), tr(fv) == tr(iv), ref(fv) == ref(iv))

# for any immediate divergence, we simply allow it to keep the existing observation.
# in order to simplify model checking, we only keep the previous value for ref (no arbitrary set)
# of course, we can further reduce the space by limiting the values for other variables

############################################
# selective healthiness conditions
############################################
# R1(P) = P and tr<=tr'
#def R1(P):
#    return And(P, prefix(tr(iv), tr(fv)))

# R3(P) = IR <| wait |> P
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
#Chaos = Process(con(R(IDiv), ok(iv), IDiv), "Chaos")

# Miracle = R(not ok)
# Miracle = R(False) |> ok <| IDiv
#Miracle = Process(con(R(False), ok(iv), IDiv), "Miracle")


# Stop = R(wait:=true)
# Stop = R(true |- tr'=tr and wait')
# Stop = R(ok' and tr'=tr and wait' and ref'=FullSet) <| ok |> IDiv
#Stop = Process(con(R(And(ok(fv), wait(fv), tr(fv) == tr(iv), ref(fv) == Fullset)), ok(iv), IDiv), "Stop")

# Skip = R(true |- tr'=tr and not wait')
# Skip = R(ok' and tr'=tr and not wait and ref'=FullSet <| ok |> IDiv)
Skip = Process(con(R(And(ok(fv), Not(wait(fv)), tr(fv) == tr(iv), ref(fv) == Fullset)), ok(iv), IDiv), "Skip")



###################################################################
# Simple Prefix, e.g., a->Skip
###################################################################
# SP(a) = R(true |- tr'=tr and a noin ref' <| wait' | tr'=tr+<a>)
# SP(a) = R(ok' and tr'=tr and a notin ref') <| wait' |> tr'=tr+<a>)

# transfrom an event (abstract data) into a string
# we use it for naming of a process
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
                                             And(diff(tr(fv),tr(iv),cons(a,nil)), ref(fv)==Fullset)))),
                       ok(iv),
                       IDiv), "SP("+EventToString(a)+")")

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
    nsp = eval(Q.expr) # nsp is a new process
    return Process(con(R(Or(And(P.relation(P.iv, P.fv), P.iv==iv, P.fv==fv, Not(ok(fv))),  # P diverges
                            And(P.relation(P.iv, P.fv), nsp.relation(nsp.iv, nsp.fv), P.iv==iv, nsp.fv==fv,
                                nsp.iv==P.fv, ok(P.fv), Not(wait(P.fv)), Not(ok(fv))),     # Q is divergent, P is not
                            And(P.relation(P.iv, P.fv), P.iv==iv, P.fv==fv, ok(fv), wait(fv)),  # P is waiting
                            And(P.relation(P.iv, P.fv), nsp.relation(nsp.iv, nsp.fv), P.iv==iv, nsp.fv==fv,
                                nsp.iv==P.fv, ok(P.fv), Not(wait(P.fv)), ok(fv)))),
                       ok(iv), IDiv), "Seq(" + P.expr + "," + Q.expr + ")")


# external choince
# P[]Q = R(¬Pff and ¬Qff |- (Ptf and Qtf) <| tr'=tr and wait' |> (Ptf or Qtf))
# P[]Q = R(Pff or Qff or (ok' and (Ptf and Qtf <| tr'=tr and wait' |> Ptf or Qtf))) <| ok |> IDiv
def EC(P,Q):
    return Process(con(R(Or(And(P.relation(P.iv,P.fv), P.iv==iv, P.fv==fv, Not(ok(fv))), # Pff
                            And(Q.relation(Q.iv,Q.fv), Q.iv==iv, Q.fv==fv, Not(ok(fv))), # Qff
                            And(ok(fv), con(And(P.relation(P.iv,P.fv),Q.relation(Q.iv,Q.fv), P.iv==iv, Q.iv==iv, ok(P.fv),
                                                wait(P.fv), tr(P.iv)==tr(P.fv), ok(Q.fv), wait(Q.fv), tr(Q.iv)==tr(Q.fv),
                                                ref(fv)==Set.intersection (ref(P.fv),ref(Q.fv))),
                                            And(tr(iv)==tr(fv), wait(fv)),
                                            Or(And(P.relation(P.iv,P.fv), P.iv==iv, P.fv==fv),
                                               And(Q.relation(Q.iv,Q.fv), Q.iv==iv, Q.fv==fv)))))),
                       ok(iv),IDiv), "EC(" + P.expr + "," + Q.expr + ")")



### Parallel Composition
### P [| A |] Q = (ok'== P.ok' and Q.ok') and (wait'== P.wait' or Q.wait') and (tr'-tr==prod(A,P.tr'-P.tr,Q.tr'-Q.tr))
###                ref' = union(inter(union(P.ref',Q.ref'),A), (inter(P.ref',Q.ref')\A)
def Par(CS, P, Q):
    r = Set.toSet(CS) # r is  the interface
    return PProcess(CS, con(R(And(P.relation(P.iv, P.fv), Q.relation(Q.iv, Q.fv), P.iv==iv, Q.iv==iv,
                                  ok(fv)==And(ok(P.fv), ok(Q.fv)), wait(fv)==Or(wait(P.fv), wait(Q.fv)),
                                  diff(tr(P.fv), tr(iv), l1), diff(tr(Q.fv), tr(iv), l2), diff(tr(fv), tr(iv), l3),
                                  parallel(global_process_index, l1, l2, l3),
                                  ref(fv)==(Set.union(Set.intersection(Set.union(ref(P.fv), ref(Q.fv)), r),
                                                      Set.difference(Set.intersection(ref(P.fv), ref(Q.fv)), r))))),
                           ok(iv), IDiv), "Par(" + str(CS) + "," + P.expr + "," + Q.expr + ")")


init = Tuple(True, False, nil, Fullset)


# deadlock free
def DLF(P):
    s = default_solver
    s.push()
    s.add(And(P.relation(P.iv, P.fv), P.iv == init, P.fv == fv, wait(fv), ref(fv)==Fullset))
    if s.check() == sat:
        print (s.model()[fv])
        print ("Deadlock!!!")
    else:
        print ("Deadlock Free!!!")
    s.pop()

# divergence free
def DVF(P):
    s = default_solver
    s.push()
    s.add(And(P.relation(P.iv, P.fv), P.iv == init, P.fv == fv, Not(ok(fv))))
    if s.check() == sat:
        print (s.model()[fv])
        print ("Divergent!!!")
    else:
        print ("Divergent Free!!!")
    s.pop()



#########################################################
#### Recursive Processes ################################
### X = RecP('Seq(SP(a),X)', 2)
### X.setup(['X'], [X])
### P = X.create()
#########################################################

#def RecP(body, round):
#    pro = body
#    for i in range(round):
#        pro = Seq(pro, body)
#    return pro

class RecP:
    def __init__(self, body, round):
        self.body = body
        self.vl = []
        self.pl = []
        self.round = round

    def setup(self, vl, pl):
        self.vl = vl
        self.pl = pl

    def create(self):
        expr = self.copy(self.round)
        return eval(expr)

    def copy(self, round):
        if round == 0:
            return 'Skip'
        else:
            body = self.body
            for i in range(len(self.pl)):
                body = body.replace(self.vl[i], self.pl[i].copy(round-1))
            return body





def ListAllTerminatedTraces(P):
    s = default_solver
    s.push()
    s.add(And(P.relation(P.iv, P.fv), P.iv == init, P.fv == fv, ok(fv), Not(wait(fv))))

    while s.check() != unsat:
        m = s.model()
        t = m[fv].children()[2]
        print (t)
        s.add(tr(fv) != t)
    s.pop()
    print ("Done")




#s = default_solver
#s.add(And(P.relation(P.iv, P.fv), P.iv == init, P.fv == fv, Not(wait(fv)), tr(fv)!=cons(a,cons(c,cons(b,cons(a,nil))))))


