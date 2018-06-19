###########################################################
### define all events and finite sets
### users need to modify this file for different processes
############################################################

from z3 import *
from finite_set import *


Channel, (input, output) = EnumSort('Channel', ('input', 'output'))

Event = Datatype('Event')
Event.declare('CE', ('channel', Channel), ('value', Channel))
Event = Event.create()
CE = Event.CE


