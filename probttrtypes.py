import ttrtypes

class Type(ttrtypes.Type):
    def __init__(self,name='',cs={}):
        super().__init__(name,cs)
        self.witness_cache = ([],[])
    def validate_witness(self, a, p):
        if self.witness_conditions == []:
            return True
        elif a in self.witness_cache[0] and isinstance(a,str):
            return True
        elif next((c for c in self.witness_conditions if c(a) is p),False):
            return True
        else:
            return False
    def judge(self, a, p):
        if a in self.witness_cache[0]:
            self.witness_cache[1][self.witness_cache[0].index(a)] = p
            return p
        elif isinstance(a,str):
            self.witness_cache[0].append(a)
            self.witness_cache[1].append(p)
            return p
        elif self.validate_witness(a,p):
            self.witness_cache[0].append(a)
            self.witness_cache[1].append(p)
            return p
        else: return False
        


