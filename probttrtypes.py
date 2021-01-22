import ttrtypes

class Type(ttrtypes.Type):
    def __init__(self,name='',cs={}):
        super().__init__(name,cs)
        self.witness_cache = ([],[])

        


