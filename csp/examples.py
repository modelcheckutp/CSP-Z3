#####################################################
## Kun Wei 26/06/2018
## uncomment the processes to use these examples
#####################################################

from csp import *
############################################################
#e1.
# P = a->Skip [] b->Skip
# Q = a->Skip |~| b->Skip

#P = EC(SP(a), SP(b))
#Q = IC(SP(a), SP(b))

# checked all traces in P as <>, <a>,<b>, and refined
#TRef(P,Q)

# unrefined, because P has (<>, {c,d}), which is not included in Q
#SFRef(P,Q)

###############################################################
#e2.
# P = a->b->Skip ||[b] b->c->Skip
#P = Par([b], Seq(SP(a),SP(b)), Seq(SP(b), SP(c)))

# show all traces
#ListAllTraces(P)

# show all traces and related refusal sets
#ListAllTracesAndRefs(P)

#deadlock checking
#DLF(P)

#deadlock checking again
#Q = Par([a,b], Seq(SP(a),SP(b)), Seq(SP(b), SP(c)))
#DLF(Q)

#################################################################
#e3.
# Hiding
# P = (a->c->Skip [] b->Skip)\{a}
# Q = c->Skip [] b-> Skip
# S = c->Skip |~| b->Skip
# Are they or two of them are same?
#P = Hide(EC(Seq(SP(a),SP(c)), SP(b)), [a])
#Q = EC(SP(c), SP(b))
#S = IC(SP(c), SP(b))

#ListAllTracesAndRefs(P)
#ListAllTracesAndRefs(Q)
#ListAllTracesAndRefs(S)

#SFRef(P,S)
#SFRef(S,P)

######################################################################
#e4.
# mutually recursive processes
# P = a->P [] b->Q
# Q = a -> Q [] b->P

#X = RecP('EC(Seq(SP(a),X), Seq(SP(b),Y))', 2)
#Y = RecP('EC(Seq(SP(a),Y), Seq(SP(b),X))', 2)
#X.setup(['X', 'Y'], [X,Y])
#Y.setup(['X', 'Y'], [X,Y])
#P = X.create()
#Q = Y.create()

#Z = RecP('EC(Seq(SP(a),Z), Seq(SP(b),Z))', 2)
#Z.setup(['Z'], [Z])
#S = Z.create()

#TRef(S, P)
#FDRef(S,P)
