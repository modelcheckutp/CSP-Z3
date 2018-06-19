###########################################################
### define all events and finite sets
### users need to modify this file for different processes
############################################################

from z3 import *
from finite_set import *

Event, (a,b,c,d,ga,gb,gc) = EnumSort('Event', ('a','b','c','d', 'ga','gb','gc'))

# defined a finite-set sort based on the declared events, then
# users can declare set variables using this new sort
SetSort = FSetSort([a,b,c,d,ga,gb,gc])

# Set is an instance of the class FSetDecl(), which can implement
# set operations such as union, intersection and so on.
Set = FSetDecl([a,b,c,d,ga,gb,gc])

# defined a fullset
Fullset = Set.fullset()

#signature events
SE = [ga,gb,gc]




