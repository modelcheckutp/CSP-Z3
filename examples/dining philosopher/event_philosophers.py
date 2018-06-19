########################################
### define all events and finite sets
########################################

from z3 import *
from finite_set import *

#Channe, (a,b,c,d) = EnumSort('Channe', ('a','b','c','d'))

N = 3

## declare channels and (compounded) events

Channel, (pickup, putdown) = EnumSort('Channel', ('pickup', 'putdown'))

Event = Datatype('Event')
Event.declare('CE', ('channel', Channel), ('phil', IntSort()), ('fork', IntSort()))
Event = Event.create()

CE = Event.CE
#channel = Event.channel
phil = Event.phil
neigh = Event.neigh




## declare finite sets
AllEvents = list(set([CE(pickup,i,i) for i in range(N)] + [CE(pickup,i,(i+1)%N) for i in range(N)] + [CE(pickup,(i-1)%N,i) for i in range(N)])) +\
            list(set([CE(putdown,i,i) for i in range(N)] + [CE(putdown,i,(i+1)%N) for i in range(N)] + [CE(putdown,(i-1)%N,i) for i in range(N)]))

#print AllEvents

SetSort = FSetSort(AllEvents)
Set = FSetDecl(AllEvents)
Fullset = Set.fullset()



