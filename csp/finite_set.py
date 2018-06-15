##################################################################
# The finite set theory based on BitVec
# Kun Wei 17/05/2017
##################################################################


from z3 import *

class FSetDecl():
    def __init__(self, l):
        self.alphabet = l
        self.size = len(l)

    def declare(self, name):
        return BitVec(name, self.size)

    def union(self, s1, s2):
        assert (s1.sort() == s2.sort())
        return s1|s2

    def intersection(self, s1, s2):
        assert (s1.sort() == s2.sort())
        return s1&s2

    def complement(self, s):
        return ~s

    def difference(self, s1, s2):
        assert (s1.sort() == s2.sort())
        return self.intersection(s1, self.complement(s2))

    def member(self, e, s):
        index = self.alphabet.index(e)
        be = BitVecVal(1, self.size)<<index
        #print(be)
        return (be & s)!= 0

    def add(self, e, s):
        index = self.alphabet.index(e)
        be = BitVecVal(1, self.size) << index
        #print(be)
        return (be | s)

    def emptyset(self):
        return BitVecVal(0, self.size)

    def fullset(self):
        return ~BitVecVal(0, self.size)

    def toElements(self, b):
        s = []
        be = BitVecVal(1,self.size)
        for i in range(self.size):
            t = simplify(b&(be<<i))
            if not (t == 0):
                s.append(self.alphabet[i])
        return s

    def toSet(self,l):
        s = self.emptyset()
        for i in range(len(l)):
            s = self.add(l[i], s)
        return s

# define a finite set sort
def FSetSort(l): # l is a list of all elements in the finite set
    return BitVecSort(len(l))


### for testing
#Channel, (a,b,c,d) = EnumSort('Channel', ('a','b','c','d'))
#FSet = FSetDecl([a,b,c,d])

#print(simplify(FSet.toSet([a,b,c])))

#s1 = FSet.declare('s1')
#s2 = FSet.declare('s2')
#s = Solver()
#s.add(s1== FSet.add(b,FSet.add(a,FSet.emptyset())))
#s.add(s2== FSet.add(c,FSet.add(a,FSet.emptyset())))

#print(FSet.toElements(BitVecVal(14,4)))
#s.add(FSet.union(s1,s2) == FSet.add(c, FSet.add(b,FSet.add(a,FSet.emptyset()))))
#s.add(FSet.intersection(s1,s2) == FSet.add(a,FSet.emptyset()) )
#s.add(FSet.complement(s1) == FSet.add(c, FSet.add(d, FSet.emptyset())))
#s.add(FSet.difference(s1,s2) == FSet.add(b, FSet.emptyset()))

#print(s.check())