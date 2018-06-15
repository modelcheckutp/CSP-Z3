###########################################################
### define all events and finite sets
### users need to modify this file for different processes
############################################################

from z3 import *
from finite_set import *

Event, (a,b,c,d) = EnumSort('Event', ('a','b','c','d'))

# defined a finite-set sort based on the declared events, then
# users can declare set variables using this new sort
SetSort = FSetSort([a,b,c,d])

# Set is an instance of the class FSetDecl(), which can implement
# set operations such as union, intersection and so on.
Set = FSetDecl([a,b,c,d])

# defined a fullset
Fullset = Set.fullset()


