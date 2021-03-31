from copy import deepcopy
from collections import deque
#from types import MethodType
from utils import gensym, some_condition, forall, forsome, substitute, show, to_latex, showall, ttracing, check_stack
from records import Rec

#==============================================================================
# Possibilities
#==============================================================================

class Possibility:
    def __init__(self,name='',d=None):
        self.name = name
        if self.name == '': self.name = gensym('M')
        if d is None:
            self.model={}
        else:
            self.model = d
    def show(self):
        return '\n'+self.name + ':\n'+'_'*45 +'\n'+ '\n'.join([show(i)+': '+show(self.model[i].witness_cache) for i in self.model if i not in ['Ty','Re','RecTy']])+'\n'+'_'*45+'\n'

_M = Possibility('_Model_')

def showmodel(m=_M):
    return show(m)

def initmodel():
    global _M
    _M.model = {}

def add_to_model(T,m=_M):
    key = T.show()
    if key in m.model:
        return m.model[key]
    else:
        m.model[key] = T
        T.poss = m
        return T




#==============================================================================
# Type classes
#==============================================================================

class TypeClass:
    def __init__(self,name='',cs={}):
        self.name = name
        if self.name == '': self.name = gensym('T')
        self.comps = Rec(cs)
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = []
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        key = self.show()
        if poss == _M:
            return self
        elif key not in poss.model:
            poss.model[key] = deepcopy(self)
            poss.model[key].poss = poss
        else:
            old = poss.model[key]
            old.witness_cache.extend([x for x in self.witness_cache if x not in old.witness_cache])
            old.supertype_cache.extend([x for x in self.supertype_cache if x not in old.supertype_cache])
            old.witness_conditions.extend([x for x in self.witness_conditions if x not in old.witness_conditions])
            old.witness_types.extend([x for x in self.witness_types if x not in old.witness_types])
        return poss.model[key]
    def show(self):
        return self.name
    def to_latex(self,vars):
        return to_latex(self.name,vars,'italic')
    def learn_witness_condition(self, c):
        if c not in self.witness_conditions:
            self.witness_conditions.append(c)
    def learn_witness_type(self,T):
        if T not in self.witness_types:
            self.witness_types.append(T)
    def validate_witness(self, a):
        if self.witness_conditions == []:
            return True
        elif a in self.witness_cache and isinstance(a,str):
            return True
        else: return some_condition(self.witness_conditions,a)
    def judge(self, a):
        if a in self.witness_cache: return True
        elif isinstance(a,str):
            self.witness_cache.append(a)
            return True
        elif self.validate_witness(a):
            self.witness_cache.append(a)
            return True
        else: return False
    def judge_nonspec(self):
        if self.witness_cache == []:
            self.create()
        return True
    def query(self, a):
        if check_stack('query', dict(a=a,self=self)):
             return '*'
        elif a in self.witness_cache: return True
        elif isinstance(a,HypObj) and show(self) in showall(a.types):
            return True
        elif isinstance(a,HypObj) and forsome(a.types,
                                              lambda T: show(self) in showall(T.supertype_cache)):
            return True
        elif isinstance(a, LazyObj):
            if isinstance(a.eval(), LazyObj):
                return a.eval().type().subtype_of(self)
            else:
                return self.query(a.eval())
        elif forsome(self.witness_types, lambda T: T.in_poss(self.poss).query(a)):
            if not isinstance(a,HypObj):
                self.witness_cache.append(a)
            return True
        else: 
            if some_condition(self.witness_conditions,a):
                if not isinstance(a,HypObj):
                    self.witness_cache.append(a)
                return True
            else:
                return False
        
    def query_nonspec(self):
        if self.witness_cache == []:
            return 'Don\'t know'
        else: return True
    def create(self):
        a = gensym('_a')
        self.judge(a)
        return a
    def create_hypobj(self):
        return HypObj([self])
    def subtype_of(self,T):
        if T in self.supertype_cache: 
            return True
        elif equal(self,T):
            return True
        else:
            a = self.create_hypobj()
            if T.query(a):
                self.supertype_cache.append(T)
                return True
            else: return False
    def subst(self,v,a):
        if self == v:
            return a
        else: return self
    def merge(self,T):
        if self.subtype_of(T):
            return self
        elif T.subtype_of(self):
            return T
        else:
            return MeetType(self,T)
    def amerge(self,T):
        if self.subtype_of(T):
            return self
        else:
            return T



def Type(name='',cs={},poss=_M):
    T = TypeClass(name,cs)
    return add_to_model(T,poss)
    

class BTypeClass(TypeClass):
    def __init__(self,name=gensym('BT')):
        self.name=name
        self.comps = Rec({})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = []
        self.witness_types = []
        self.poss = _M

def BType(name=gensym('BT'),poss=_M):
    T = BTypeClass(name)
    return add_to_model(T,poss)

    
class PTypeClass(TypeClass):
    def __init__(self,pred,args): 
        self.comps = Rec({'pred':pred, 'args':args})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = []
        self.witness_types = []
        self.poss = ''
    def show(self):
        return self.comps.pred.name+'('+', '.join([show(x) for x in self.comps.args])+')'
    def to_latex(self,vars):
        return '\\text{'+self.comps.pred.name+'}'+'('+', '.join([to_latex(x,vars) for x in self.comps.args])+')'
    def validate(self):
        if isinstance(self.comps.pred,Pred) \
                and len(self.comps.args) == len(self.comps.pred.arity):
            for i in zip(self.comps.args,self.comps.pred.arity):
                if i[1].query(i[0]) == True: pass
                else: return False
            return True
        else: return False
    def create(self):
        e = gensym('_e')
        self.judge(e)
        return e
    def subst(self,v,a):
        if self == v:
            return a
        else:
            newargs = []
            for arg in self.comps.args:
                if arg == v: newargs.append(a)
                elif isinstance(arg,str): newargs.append(arg)
                else: newargs.append(substitute(arg,v,a))      #arg.subst(v,a))
            return PType(self.comps.pred,newargs).in_poss(self.poss)
    def eval(self):
        newargs = []
        for arg in self.comps.args:
            if 'eval' in dir(arg):
                newargs.append(arg.eval())
            else:
                newargs.append(arg)
        self.comps.args = newargs
        return self
    def query(self,a):
        # print('super',super().query(a))
        # if super().query(a):
        #     print('super',super().query(a))
        #     return True
        if check_stack('query', dict(a=a,self=self)):
             return '*'
        elif a in self.witness_cache: return True
        elif isinstance(a,HypObj) and show(self) in showall(a.types):
            return True
        elif isinstance(a,HypObj) and forsome(a.types,
                                              lambda T: show(self) in showall(T.supertype_cache)):
            return True
        elif isinstance(a, LazyObj):
            if isinstance(a.eval(), LazyObj):
                return a.eval().type().subtype_of(self)
            else:
                return self.query(a.eval())
        elif forsome(self.witness_types, lambda T: T.in_poss(self.poss).query(a)):
            if not isinstance(a,HypObj):
                self.witness_cache.append(a)
            return True
        elif some_condition(self.witness_conditions,a):
            if not isinstance(a,HypObj):
                self.witness_cache.append(a)
            return True
        # elif self.poss == '' and forsome(self.comps.pred.witness_funs, lambda f: f(self.comps.args).query(a)):
        #     if not isinstance(a, HypObj):
        #         self.witness_cache.append(a)
        #     return True
        elif forsome(self.comps.pred.witness_funs, lambda f: f(self.comps.args).in_poss(self.poss).query(a)):
            if not isinstance(a, HypObj):
                self.witness_cache.append(a)
            return True
        else:
            return False

def PType(pred,args,poss=_M):
    T = PTypeClass(pred,args)
    return add_to_model(T,poss)
            
    
class MeetType(TypeClass):
    def __init__(self,T1,T2): 
        self.comps = Rec({'left':T1, 'right':T2})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda a: self.comps.left.in_poss(self.poss).query(a) \
                                       and self.comps.right.in_poss(self.poss).query(a)]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
        
    def show(self):
        return '('+ self.comps.left.show()+'&'+self.comps.right.show()+')'
    def to_latex(self,vars):
        return '\\left(\\begin{array}{rcl}\n'+ self.comps.left.to_latex(vars)+'\land'+self.comps.right.to_latex(vars)+'\n\\end{array}\\right)'
    def learn_witness_condition(self,c):
        if ttracing('learn_witness_condition'):
            print('Meet types are logical and cannot learn new conditions')
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.left, TypeClass) \
                and isinstance(self.comps.right, TypeClass):
            return True
        else: return False
    def judge(self,a):
        if self.comps.left.judge(a) and self.comps.right.judge(a):
            return True
        else:
            return False
    def judge_nonspec(self):
        if self.witness_cache == [] and [x for x in self.comps.left.witness_cache if x in self.comps.right.witness_cache] == []:
            new = self.comps.left.create()
            self.comps.right.judge(new)
            self.judge(new)
        return True
    def create(self):
        a = self.comps.left.create()
        self.comps.right.judge(a)
        self.witness_cache.append(a)
        return a
    def create_hypobj(self):
        return HypObj([self.comps.left,self.comps.right,
                       self.comps.left.merge(self.comps.right)])
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return MeetType(self.comps.left.subst(v,a),self.comps.right.subst(v,a)).in_poss(self.poss)



class JoinType(TypeClass):
    def __init__(self,T1,T2): 
        self.comps = Rec({'left':T1, 'right':T2})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda a: self.comps.left.in_poss(self.poss).query(a), \
                                       lambda a: self.comps.right.in_poss(self.poss).query(a)]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return '('+ self.comps.left.show()+'v'+self.comps.right.show()+')'
    def to_latex(self,vars):
        return '\\left(\\begin{array}{rcl}\n'+ self.comps.left.to_latex(vars)+'v'+self.comps.right.to_latex(vars)+'\n\\end{array}\\right)'
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.left, TypeClass) \
                and isinstance(self.comps.right, TypeClass):
            return True
        else: return False
    def judge(self, a):
        if a in self.witness_cache: return True
        else:
            self.witness_cache.append(a)
            return True
    def subtype_of(self,T):
        if T in self.supertype_cache:
            return True
        elif equal(self,T):
            return True
        else:
            if self.comps.left.subtype_of(T) and self.comps.right.subtype_of(T):
                return True
            else:
                return False
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return JoinType(self.comps.left.subst(v,a),self.comps.right.subst(v,a))


        
class FunType(TypeClass):
    def __init__(self,T1,T2): 
        self.comps = Rec({'domain':T1, 'range':T2})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda f: isinstance(f,Fun) \
                                        and f.domain_type == self.comps.domain \
                                        and self.comps.range.query(f.app(self.comps.domain.create_hypobj()))]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        return self
    def show(self):
        return '('+ self.comps.domain.show() + '->' + self.comps.range.show()+')'
    def to_latex(self,vars):
        return '\\left(\\begin{array}{rcl}\n'+ to_latex(self.comps.domain,vars) + '->' + to_latex(self.comps.range,vars)+'\n\\end{array}\\right))'
    
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.domain, TypeClass) \
                and isinstance(self.comps.range, TypeClass):
            return True
        else: return False
    # def create_hypobj(self):
    #     return Fun(gensym('x'),self.comps.domain,self.comps.range.create_hypobj())
    def subst(self,v,a):
        if self == v:
            return a
        else: return FunType(self.comps.domain.subst(v,a),self.comps.range.subst(v,a))



class ListType(TypeClass):
    def __init__(self,T):
        self.comps = Rec({'base_type':T})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda l: isinstance(l,list) and forall(l, lambda x: T.in_poss(self.poss).query(x))]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return '['+ show(self.comps.base_type)+']'
    def to_latex(self,vars):
        return '\\left[\\begin{array}{rcl}\n'+ to_latex(self.comps.base_type,vars)+'\n\\end{array}\\right]'
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.base_type,TypeClass):
            return True
        else: return False
    def subst(self,v,a):
        if self == v:
            return a
        else: return ListType(substitute(self.comps.base_type,v,a))



class SingletonType(TypeClass):
    def __init__(self,T,a):
        self.comps = Rec({'base_type':T, 'obj':a})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [lambda x: show(x) == show(a) and T.query(x),\
                                   lambda x: isinstance(a,LazyObj)\
                                             and show(x) == show(a.eval()) and T.in_poss(self.poss).query(x)]
        self.witness_types = []
        self.poss = _M 
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return show(self.comps.base_type)+'_'+ show(self.comps.obj)
    def to_latex(self,vars):
        return to_latex(self.comps.base_type,vars)+'_{'+ to_latex(self.comps.obj,vars)+'}'
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def validate(self):
        if isinstance(self.comps.base_type,TypeClass):
            return True
        else: return False
    def create(self):
        self.judge(self.comps.obj)
        return self.comps.obj
    def create_hypobj(self):
        if 'eval' in dir(self.comps.obj):
            return self.comps.obj.eval()
        else:
            return self.comps.obj
    def subst(self,v,a):
        if self == v:
            return a
        else: return SingletonType(substitute(self.comps.base_type,v,a),substitute(self.comps.obj,v,a))



class RecType(TypeClass):
    def __init__(self,d={}):
        self.comps = Rec()
        for item in d.items():
            if isinstance(item[1], dict):
                self.addfield(item[0], RecType(item[1]))
            else:
                self.addfield(item[0], item[1])
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = [ \
            lambda r: isinstance(r, Rec) and RecOfRecType(r,self,self.poss)]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        s = ""
        for kvp in self.comps.__dict__.items():           
            if s == "":
                s = s + kvp[0] + " : "
            else:
                s = s + ", "+kvp[0] + " : "
            
            if(isinstance(kvp[1], RecType)):
                 s = s + kvp[1].show()                
            else:
                s = s + show(kvp[1]) 
        return "{"+s+"}"
    
    def to_latex(self,vars):
        s = ""
        for kvp in self.comps.__dict__.items():           
            if s == "":
                s = s + to_latex(kvp[0]) + " &:& "
            else:
                s = s + "\\\\\n"+to_latex(kvp[0]) + " &:& "
            
            if(isinstance(kvp[1], RecType)):
                 s = s + kvp[1].to_latex(vars)                
            else:
                s = s + to_latex(kvp[1],vars,anglebrackets="yes") 
        return "\\left[\\begin{array}{lcl}\n"+s+"\n\\end{array}\\right]"

    def validate(self):
        if forall(list(self.comps.__dict__.items()),lambda x: CheckField(x,self)) and not self.create_hypobj() == None:
            return True
        else:
            return False
        
        
    def addfield(self, label, value):
        if label in self.comps.__dict__.keys(): 
            print("\"" +label + "\"" + " is already a label in this record type")
        else: 
            self.comps.__setattr__(label, value)
    
    # def pathvalue(self,path):
    #     if len(path) == 1: 
    #         return self.comps.__getattribute__(str(path[0]))
    #     else: 
    #         return Rec.pathvalue(self.comps.__getattribute__(path[0]), path[1:])
            
    def pathvalue(self, path):
        splits=deque(path.split("."))
        if (len(splits) == 1):
            if splits[0] in dir(self.comps):
                return self.comps.__getattribute__(splits[0])
            else:
                if ttracing('pathvalue'):
                    print(splits[0]+' not a label in '+self.show())
                return None
        else:
            addr = splits.popleft()
            if 'pathvalue' not in dir(self.comps.__getattribute__(addr)):
                if ttracing('pathvalue'):
                    print('No paths into '+show(self.comps.__getattribute__(addr)))
                return None
            else:
                return self.comps.__getattribute__(addr).pathvalue(".".join(splits))
    def learn_witness_condition(self,c):
        logtype(self,c)
    def learn_witness_type(self,c):
        logtype_t(self,c)
    def create(self):
        res = Rec()
        depfields = RecType()
        for l in self.comps.__dict__:
            T = self.comps.__getattribute__(l)
            if isinstance(T,TypeClass):
                res.addfield(l,T.in_poss(self.poss).create())
            else: depfields.addfield(l,T)
        return ProcessDepFields(depfields,res,self)
        
    def create_hypobj(self):
        res = Rec()
        depfields = RecType()
        for l in self.comps.__dict__:
            T = self.comps.__getattribute__(l)
            if isinstance(T,TypeClass):
                res.addfield(l,T.create_hypobj())
            else: depfields.addfield(l,T)
        return ProcessDepFields(depfields,res,self,'hyp')
        

        
    
    #Recursive for future use??            
    def Relabel(self, oldlabel, newlabel, recursive=False):
        if oldlabel in self.comps.__dict__.keys():
            value = self.comps.__dict__[oldlabel]
            self.comps.__delattr__(oldlabel)
            self.comps.__setattr__(newlabel, value)
        return
    
    def subst(self,v,a):
        res = RecType()
        for l in self.comps.__dict__.keys():
            if self.comps.__getattribute__(l) == v:
                res.addfield(l,a)
            elif isinstance(self.comps.__getattribute__(l),str):
                res.addfield(l,self.comps.__getattribute__(l))
            else: 
                res.addfield(l,substitute(self.comps.__getattribute__(l),v,a))
        #print(show(res))
        return res

    def eval(self):
        self.comps.eval()
        return self

    def merge(self,T):
        if isinstance(T,RecType):
            res = RecType({})
            SharedLabels = [l for l in LabelsRecType(self) if l in LabelsRecType(T)]
            OtherLabelsSelf = [l for l in LabelsRecType(self) if l not in LabelsRecType(T)]
            OtherLabelsT = [l for l in LabelsRecType(T) if l not in LabelsRecType(self)]
            for label in SharedLabels:
                T1 = AttValRecType(self,label)
                T2 = AttValRecType(T,label)
                if isinstance(T1, tuple) and isinstance(T2, tuple):
                    if T1[1] == T2[1]:
                        f1 = T1[0]
                        f2 = T2[0]
                        res.addfield(label, (merge_dep_types(f1,f2),T1[1]))
                    else:
                        f1 = T1[0]
                        f2 = T2[0]
                        res.addfield(label, (combine_dep_types(f1,f2),T1[1]+T2[1]))
                elif isinstance(T1,tuple) and isinstance(T2,TypeClass):
                    res.addfield(label, (combine_dep_types(T1[0],T2),T1[1]))
                elif isinstance(T1,TypeClass) and isinstance(T2,tuple):
                    res.addfield(label, (combine_dep_types(T1,T2[0]),T2[1]))
                else:
                    res.addfield(label, T1.merge(T2))
            for label in OtherLabelsSelf:
                res.addfield(label,AttValRecType(self,label))
            for label in OtherLabelsT:
                res.addfield(label,AttValRecType(T,label))
            return res
        elif self.subtype_of(T):
            return self
        else:
            return MeetType(self,T)
    def amerge(self,T):
        if isinstance(T,RecType):
            res = RecType({})
            SharedLabels = [l for l in LabelsRecType(self) if l in LabelsRecType(T)]
            OtherLabelsSelf = [l for l in LabelsRecType(self) if l not in LabelsRecType(T)]
            OtherLabelsT = [l for l in LabelsRecType(T) if l not in LabelsRecType(self)]
            for label in SharedLabels:
                T1 = AttValRecType(self,label)
                T2 = AttValRecType(T,label)
                if isinstance(T1, tuple) and isinstance(T2, tuple):
                    if T1[1] == T2[1]:
                        f1 = T1[0]
                        f2 = T2[0]
                        if subtype_of_dep_types(f1,f2):
                            res.addfield(label, T1)
                        else:
                            res.addfield(label, T2)
                    else:
                        res.addfield(label, T2)
                elif isinstance(T1,tuple) and isinstance(T2,TypeClass):
                    res.addfield(label, T2)
                elif isinstance(T1,TypeClass) and isinstance(T2,tuple):
                    res.addfield(label,T2)
                elif isinstance(T1,TypeClass) and isinstance(T2,TypeClass):
                    if T1.subtype_of(T2):
                        res.addfield(label, T1)
                    else:
                        res.addfield(label, T1.amerge(T2))
                else:
                   res.addfield(label,T2) 
            for label in OtherLabelsSelf:
                res.addfield(label,AttValRecType(self,label))
            for label in OtherLabelsT:
                res.addfield(label,AttValRecType(T,label))
            return res
        elif self.subtype_of(T):
            return self
        else:
            return T

def LabelsRecType(T):
    if isinstance(T, RecType):
        return T.comps.__dict__.keys()
    else:
        print('LabelsRecType not defined on '+ show(T) +' (not a record type)')
        return None

def AttValRecType(T,l):
    if isinstance(T, RecType):
        return T.comps.__getattribute__(l)
    else:
        print('AttValRecType not defined on '+show(T)+' (not a record type)')
        return None
       
def RecOfRecType(r,T,M):
    TypeLabels = [l for l in T.comps.__dict__]
    RecordLabels = [l for l in r.__dict__]
    if forsome(TypeLabels, lambda l: l not in RecordLabels):
        return False
    elif forall(TypeLabels, lambda l: l in RecordLabels and QueryField(l,r,T,M)):
        return True
    else:
        return False

def QueryField(l,r,T,M):
    TInField = T.comps.__getattribute__(l)
    Obj = r.__getattribute__(l)
    if isinstance(Obj,HypObj):  # Should this be removed now?
        M = _M
    if isinstance(TInField, TypeClass):
        return TInField.in_poss(M).query(Obj) 
    else:
        TResolved = ComputeDepType(r,TInField,M)
        return TResolved.in_poss(M).query(Obj)

def ComputeDepType(r, DepType, M):
    if DepType[1] == []:
        #print(show(DepType[0]))
        return DepType[0]
    else:
        pth = DepType[1][0]
        if isinstance(pth,AbsPath):
            newfun = DepType[0].appc_m(pth.rec.pathvalue(pth.path), M)
        else:
            newfun = DepType[0].appc_m(r.pathvalue(DepType[1][0]), M)
        #print(show(newfun))
        return ComputeDepType(r, (newfun, DepType[1][1:]), M)

def CheckField(i,RecT):
    if isinstance(i[1], tuple): 
        return CheckPathList(i[1][1],RecT) 
    elif isinstance(i[1],RecType):
        return i[1].validate()
    else:
        return True

def CheckPathList(Paths, RecT):
    return forall(Paths, lambda x: CheckPath(x,RecT))
           
def CheckPath(path,RecT):
    if isinstance(path, AbsPath):
        return CheckPath(path.path,path.rec)
    else:
        res = RecT.pathvalue(path)
        if res == None:
            #print(res)
            return False
        else: return True

def ProcessDepFields(depfields,res,rtype,mode='real'):
    if len(depfields.comps.__dict__) == 0:
        return res
    else:
        oldlength = len(depfields.comps.__dict__)
        todelete = []
        for l in depfields.comps.__dict__:
            Resolved = ComputeDepType(res,depfields.comps.__getattribute__(l),rtype.poss)
            #print(show(Resolved))
            if 'not a label' in show(Resolved):  #Is this condition still used?
                pass
            elif Resolved == None:
                pass
            else:
                if mode=='real':
                    res.addfield(l,Resolved.in_poss(rtype.poss).create())
                    todelete.append(l)
                elif mode=='hyp':
                    res.addfield(l,Resolved.create_hypobj())
                    todelete.append(l)
                else:
                    print(mode+' not recognized as option for ProcessDepFields')
        for l in todelete:
            del depfields.comps.__dict__[l]
        if len(depfields.comps.__dict__) < oldlength:
            return ProcessDepFields(depfields,res,rtype,mode)
        else:
            if ttracing('create') or ttracing('create_hypobj'):
                print('Unresolved dependency in '+show(rtype))
            return None
                                
class TTRStringType(TypeClass):
    def __init__(self,list_of_types):
        self.comps = Rec({'types' : list_of_types})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = \
          [lambda s: isinstance(s,TTRString) \
           and len(s.items) == len(self.comps.types) \
           and forall([x for x in range(len(self.comps.types))], \
                      lambda i: self.comps.types[i].in_poss(self.poss).query(s.items[i]))]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        return '^'.join([show(i) for i in self.comps.types])
    def to_latex(self,vars):
        # TODO
        return '⁀'.join([to_latex(i,vars) for i in self.comps.types])
    def validate(self):
        return forall(self.comps.types, lambda T: isinstance(T,TypeClass))
    def learn_witness_condition(self,c):
        logtype(self,c)
        return None
    def learn_witness_type(self,c):
        logtype_t(self,c)
        return None
    def create(self):
        return TTRString([T.create() for T in self.comps.types])
    def create_hypobj(self):
        return TTRString([T.create_hypobj() for T in self.comps.types])
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return TTRStringType(substitute(self.comps.types,v,a))
    def merge(self,T):
        if self.subtype_of(T):
            return self
        elif T.subtype_of(self):
            return T
        elif isinstance(T,TTRStringType) and len(T.comps.types)==len(self.comps.types):
            return TTRStringType([self.comps.types[i].merge(T.comps.types[i])
                                  for i in range(len(self.comps.types))])
        else:
            return MeetType(self,T)
    def amerge(self,T):
        if self.subtype_of(T):
            return self
        elif isinstance(T,TTRStringType) and len(T.comps.types)==len(self.comps.types):
            return TTRStringType([self.comps.types[i].amerge(T.comps.types[i])
                                  for i in range(len(self.comps.types))])
        else:
            return T

         
class KPlusStringType(TypeClass):
    def __init__(self,strT):
        self.comps = Rec({'base_type' : strT})
        self.witness_cache = []
        self.supertype_cache = []
        self.witness_conditions = \
          [lambda s: isinstance(s,TTRString) and s.startswith_recursive(self.comps.base_type)]
           # and len(s.items)>0 \
           # and forall(s.items,
           #            lambda a: self.comps.base_type.in_poss(self.poss).query(a))]
        self.witness_types = []
        self.poss = _M
    def in_poss(self,poss):
        self.poss = poss
        return self
    def show(self):
        if isinstance(self.comps.base_type, TTRStringType) and len(self.comps.base_type.comps.types)>1:
            return '('+show(self.comps.base_type)+')+'
        else:
            return show(self.comps.base_type)+'+'
    def to_latex(self,vars):
        if isinstance(self.comps.base_type, TTRStringType) and len(self.comps.base_type.comps.types)>1:
            return '('+to_latex(self.comps.base_type)+')^+'
        else:
            return to_latex(self.comps.base_type)+'^+'
    def validate(self):
        return isinstance(self.comps.base_type, TypeClass)
    def learn_witness_condition(self,c):
        logtype(self,c)
        return None
    def learn_witness_type(self,c):
        logtype_t(self,c)
        return None
    def create(self):
        a = gensym('_sigma')
        self.judge(a)
        return(a)
    def subtype_of(self,T):
        if T in self.supertype_cache: 
            return True
        elif equal(self,T):
            return True
        elif isinstance(T,KPlusStringType) and self.comps.base_type.subtype_of(T.comps.base_type):
            return True
        else:
            a = self.create_hypobj()
            if T.query(a):
                self.supertype_cache.append(T)
                return True
            else: return False
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return KPlusStringType(substitute(self.comps.base_type,v,a))
    def merge(self,T):
        if self.subtype_of(T):
            return self
        elif T.subtype_of(self):
            return T
        elif isinstance(T,KPlusStringType):
            return KPlusStringType(self.comps.base_type.merge(T.comps.base_type))
        else:
            return MeetType(self,T)
 
#==============================================================================
# Types       
#==============================================================================
  
Ty = Type('Ty') 
Ty.witness_conditions = [lambda T : isinstance(T,TypeClass)]
def logtype(x,c): 
    if ttracing('learn_witness_condition'):
        print(show(x)+' is a logical type and cannot learn new conditions')
def logtype_t(x,c): 
    if ttracing('learn_witness_type'):
        print(show(x)+' is a logical type and cannot learn new conditions')
Ty.learn_witness_condition = logtype.__get__(Ty,Ty.__class__)
Ty.learn_witness_type = logtype_t.__get__(Ty,Ty.__class__)
def create_method_type(self):
    a = gensym('_T')
    self.judge(a)
    return a
Ty.create = create_method_type.__get__(Ty, Ty.__class__)#MethodType(create_method_type,Ty,Type)

Re = Type('Re')
Re.witness_conditions = [lambda r: isinstance(r,Rec)]
Re.learn_witness_condition = logtype.__get__(Re,Re.__class__)
Re.learn_witness_type = logtype_t.__get__(Re,Re.__class__)
def create_method_rec(self):
    a = gensym('_r')
    self.judge(a)
    return a
Re.create = create_method_rec.__get__(Re, Re.__class__)#MethodType(create_method_rec,Re,Type)

RecTy = Type('RecTy')
RecTy.witness_conditions = [lambda T: isinstance(T,RecType)]
RecTy.supertype_cache = [Ty]
RecTy.learn_witness_condition = logtype.__get__(RecTy,RecTy.__class__)
RecTy.learn_witness_type = logtype_t.__get__(RecTy,RecTy.__class__)
RecTy.create = create_method_type.__get__(RecTy, RecTy.__class__)#MethodType(create_method_type,RecTy,Type)

#==============================================================================
# Non-type classes
#==============================================================================

class Pred:
    def __init__(self,name,arity):
        self.name = name
        self.arity = arity
        self.witness_funs = []
    def show(self):
        return self.name
    def to_latex(self,vars):
        return to_latex(self.name,vars)#.replace('_', '\\_')
    def learn_witness_fun(self,f):
        if f not in self.witness_funs:
            self.witness_funs.append(f)
        
class Fun(object):
    def __init__(self,v,dom,body):
        self.__setattr__('var',v)
        self.__setattr__('domain_type',dom)
        self.__setattr__('body',body)
    def show(self):
        return 'lambda ' + self.var + ':' + self.domain_type.show() + ' . ' + show(self.body)
    def to_latex(self,vars):
        vars = vars+[self.var]
        return '\\lambda ' + to_latex(self.var,vars) + ':' + to_latex(self.domain_type,vars) + '\\ .\\ ' + to_latex(self.body,vars)
    def validate(self):
        if isinstance(self.var,str) and isinstance(self.domain_type,TypeClass):
            return True
        else: return False
    def validate_arg(self,arg):
        return self.domain_type.query(arg)
    def validate_arg_m(self,arg,M):
        return self.domain_type.in_poss(M).query(arg)
    def app(self,arg):
        if self.var == self.body: 
            return arg
        else: 
            res = substitute(self.body,self.var,arg)
            if 'cache' in dir(res) and not isinstance(arg,HypObj):
                return res.cache() #This conditional not used?
            elif 'eval' in dir(res):
                return res.eval()
            # elif isinstance(res,HypObj):
            #     res.depends_on.append(arg)
            #     return res
            else:
                return res
    def appc(self,arg):
        if self.validate_arg(arg):
            return self.app(arg)
        else:
            if ttracing('appc'):
                print (self.show()+'('+show(arg)+'): badly typed function application')
            return None
    def appc_m(self,arg,M):
        if self.validate_arg_m(arg,M):
            return self.app(arg)
        else:
            if ttracing('appc_m'):
                print (self.show()+'('+show(arg)+'): badly typed function application')
            return None            
                
    def subst(self,v,a):
        if self.var == v:
            return self  # v is bound and not replaced
        else: return Fun(self.var,substitute(self.domain_type,v,a),substitute(self.body,v,a))
    def in_poss(self,M):
        self.domain_type = self.domain_type.in_poss(M)
        return self

def merge_dep_types(f1,f2):
    if isinstance(f1,TypeClass) and isinstance(f1,TypeClass):
        return f1.merge(f2)
    elif isinstance(f1,Fun) and isinstance(f2,Fun):
        var = gensym('v')
        return Fun(var, f1.domain_type.merge(f2.domain_type),
                   merge_dep_types(f1.body.subst(f1.var,var),f2.body.subst(f2.var,var)))
    else:
        if ttracing('merge_dep_types'):
            print(show(f1)+' and '+show(f2)+' cannot be merged.')
        return None


def combine_dep_types(f1,f2):
    if isinstance(f1,TypeClass) and isinstance(f2,TypeClass):
        return f1.merge(f2)
    elif isinstance(f1,Fun) and isinstance(f2,TypeClass):
        var = gensym('v')
        return Fun(var, f1.domain_type, combine_dep_types(f1.body.subst(f1.var,var),f2))
    elif isinstance(f1,TypeClass) and isinstance(f2,Fun):
        var = gensym('v')
        return Fun(var, f2.domain_type, combine_dep_types(f1,f2.body.subst(f2.var,var)))
    elif isinstance(f1,Fun) and isinstance(f2,Fun):
        var1 = gensym('v')
        var2 = gensym('v')
        return Fun(var1, f1.domain_type,
                   Fun(var2, f2.domain_type, combine_dep_types(f1.body.subst(f1.var,var1),f2.body.subst(f2.var,var2))))
    else:
        if ttracing('combine_dep_types'):
            print(show(f1)+' and '+show(f2)+' cannot be combined.')
        return None

def subtype_of_dep_types(f1,f2):
    if isinstance(f1,TypeClass) and isinstance(f2,TypeClass):
        return f1.subtype_of(f2)
    elif isinstance(f1,Fun):
        f1inst = f1.app(f1.domain_type.create_hypobj())
        return subtype_of_dep_types(f1inst,f2)
    elif isinstance(f2,Fun):
        f2inst = f2.app(f2.domain_type.create_hypobj())
        return subtype_of_dep_types(f1,f2inst)
    else:
        if ttracing('subtype_of_dep_types'):
            print(show(f1)+ ' and '+show(f2)+' cannot be compared for subtyping.')
        return None
    

class HypObj(object):
    def __init__(self,types):
        self.types = types
        #self.depends_on = []
        self.name = gensym('h')
    def validate(self):
        return forall(self.types,lambda x: isinstance(x,TypeClass))
    def show(self):
        return self.name
    def to_latex(self,vars):
        return self.name

class LazyObj(object):
    def __init__(self,strlist):
        self.oplist = strlist
    def subst(self,v,a):
        self.oplist = substitute(self.oplist,v,a)
        return self.eval()
    def eval(self):
        if isinstance(self.oplist[0],list) and\
                self.oplist[1] == '+' and\
                isinstance(self.oplist[2],list):
            return self.oplist[0] + self.oplist[2]
        elif isinstance(self.oplist[0],Fun) and\
                self.oplist[1] == '@':
            return self.oplist[0].app(self.oplist[2])
        elif isinstance(self.oplist[0],Rec) and\
                self.oplist[1] == '.':
            return self.oplist[0].__getattribute__(self.oplist[2])
        elif isinstance(self.oplist[0],LazyObj):
            oldoplist = self.oplist
            self.oplist = [self.oplist[0].eval(),self.oplist[1],self.oplist[2]]
            if not oldoplist == self.oplist:
                return self.eval()
            else:
                return self
        else: return self
    def type(self):
        if self.oplist[1] == '@':
            if 'types' in [x for x in dir(self.oplist[0])
                           if x in dir(self.oplist[2])]:
                return ti_apply(self.oplist[0].types[0],
                                self.oplist[2].types[0])
            else:
                pass
        else:
            print('Unable to compute type of ' + show(self))
            return None
    def show(self):
        return show(self.oplist)
    def to_latex(self,vars):
        return to_latex(self.oplist[0],vars)+to_latex(self.oplist[1],vars)+to_latex(self.oplist[2],vars)



class AbsPath(object):
    def __init__(self,rec,path):
        self.rec = rec
        self.path = path
    def show(self):
        return show(self.rec)+'.'+show(self.path)
    def to_latex(self,vars):
        return to_latex(self.rec,vars)+'.'+to_latex(self.path,vars)
    def subst(self,v,a):
        return AbsPath(substitute(self.rec,v,a),substitute(self.path,v,a))

class TTRString(object):
    def __init__(self,list):
        self.items = list
    def concat(self,s):
        if isinstance(s, TTRString):
            return TTRString(self.items+s.items)
        else:
            return TTRString(self.items+[s])
    def startswith(self,T):
        firstT = next(filter(lambda x: T.query(x),[TTRString(self.items[0:i+1]) for i in range(len(self.items))]),None)
        if firstT:
            return TTRString(self.items[len(firstT.items):])
        else:
            return False
                             
            
        # for i in range(len(self.items)):
        #     if T.query(TTRString(self.items[0:i+1])):
        #         return(TTRString(self.items[i+1:]))
        #     else:
        #         pass
        # return(False)
    def startswith_recursive(self,T):
        res = self.startswith(T)
        if res is False:
            return(res)
        elif res.items == []:
            return(True)
        else:
            return(res.startswith_recursive(T))
    def show(self):
        return '"'+' '.join([show(i) for i in self.items])+'"'
    def to_latex(self,vars):
        return '\ '.join([to_latex(i,vars) for i in self.items])

#============================

# Equality

#============================

def equal(x,y):
    # if show(x) == show(y):
    #     return True
    # else:
    #     return False
    if 'poss' in dir(x) and 'poss' in dir(y):
        return x.poss == y.poss and show(x) == show(y)
    else:
        return show(x) == show(y)


#============================

# Type inference

#============================

def ti_apply(Tf, Targ):
    if isinstance(Tf, FunType) \
        and Targ.subtype_of(Tf.comps.domain):
        return Tf.comps.range
    else:
        if ttracing('ti_apply'):
            print('Not a well-typed function application: '+ show(Tf) + show(Targ))
        return None
    

#=============================

# Errors 


#==============================

class FunctionApplicationError(Exception):
    pass

