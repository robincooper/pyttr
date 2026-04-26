import ttrtypes as ttr
import records as rec
#from records import Rec
from neurons import ActivityPattern, merge_apat_list, GensymNeuronTable
from utils import gensym, show, substitute

#####################################

# Global tables

#####################################

class Iota(object):
    def __init__(self):
        self.dict = {}
    def add_grandmother(self,obj,network):
        if obj not in self.dict:
            self.dict[obj] = Type_n(obj)
        network.add_neuron(obj)
        self.dict[obj].add_apat(network,ActivityPattern([[len(network.neurons)-1]]))
    def gettype_n(self,obj):
        return self.dict[obj]

gensym_n = GensymNeuronTable()
iota = Iota()
labels = Iota()
recs = {}

####################################

# nu function

####################################

def nu(a,assgn=None):
    if 'nu' in dir(a):
        return a.nu(assgn)
    elif isinstance(a,list):
        postypes = [nu(i,assgn) for i in a]
        negtypes = [InhibitType_n(T,assgn) for T in postypes]
        return StringType_n([postypes[0]]+
                            [MeetType_n(T1,T2,assgn)
                             for T1,T2 in zip(negtypes[:-1],postypes[1:])]+
                            [negtypes[-1]],assgn)
    elif isinstance(a,tuple):
        return nu(list(a),assgn)
    elif a in iota.dict:
        return iota.gettype_n(a)
    elif a in labels.dict:
        return labels.gettype_n(a)
    elif isinstance(a,Rec):
        return recs[a]
    elif isinstance(a,str) and '.' in a:
        return StringType_n([nu(i,assgn) for i in a.split('.')],assgn)
    else:
        print('Function "nu" not defined for '+ttr.show(a))
        return None


#####################################

# Type classes

#####################################

class Type(ttr.TypeClass):
    def __init__(self,name='',cs={},nu=None):
        ttr.TypeClass.__init__(self,name,cs)
        self.fixed_nu = nu
    def nu(self,assgn):
        # if self.fixed_nu is None:
        #     return Type_n(self.name+'_n',assgn=assgn)
        # else:
        #     return self.fixed_nu
        if self.fixed_nu is None:
            self.fixed_nu = Type_n(self.name+'_n')
        return self.fixed_nu
    def aus_prop(self,obj):
        return(Rec({'l_type':self,'l_obj':obj}))

class Type_n(ttr.TypeClass):
    def __init__(self,name='',cs={},assgn=None):
        ttr.TypeClass.__init__(self,name,cs)
        self.apats = {}
        self.to_inhibit = [self]
        self.assgn = assgn
    def add_apat(self,network,apat):
        self.apats[network.name] = apat
    def getapat(self,network):
        return self.apats[network.name]
    def show_apat(self,network):
        apat = self.getapat(network)
        l = [zip(i,j) for i,j in zip(apat.neurons,apat.vals)]
        return [[(x,network.neurons[x].name,y) for x,y in l[i]] for i in range(len(l))]
    # def getjudgmnt_apat(self,a,network):
    #     a_nu = nu(a)
    #     on = self.getapat(network).merge(a_nu.getapat(network))
    #     off = InhibitType_n(self).getapat(network).merge(InhibitType_n(a_nu).getapat(network))
    #     return on.concat(off)
    def add_grandmother(self,network):
        n = network.add_neuron(self.name)
        self.apats[network.name] = ActivityPattern([[len(network.neurons)-1]])
        return n
    def add_switch_grandmother(self,network):
        n = network.add_switch_neuron(self.name)
        self.apats[network.name] = ActivityPattern([[len(network.neurons)-1]])
        return n
    def create_n(self,network):
        network.realize_apat(self.getapat(network))
    def inhibit_n(self,network):
        network.inhibit_apat(self.getapat(network))
    def query_n(self,network):
        return network.match_apat(self.getapat(network))
    def query_last_n(self,network):
        apat = self.getapat(network)
        return network.match_apat(apat,network.history[-len(apat.neurons):])
    def judgmnt_type_n(self,objn,assgn=None):
        T_n = MeetType_n(self,objn,assgn)
        return StringType_n([T_n,InhibitType_n(T_n)],assgn)
    def subtype_of_n(self,T_n,network):
        network.nontrace()
        network.ntrace()
        T_n.create_n(network)
        return network.match_apat(self.getapat(network))




class InhibitType_n(Type_n):
    def __init__(self,T,assgn=None):
        self.comps = rec.Rec({'base_type':T})
        self.to_inhibit = []
    def getapat(self,network):
        inhibit_apat_list = [i.getapat(network) for i in
                             self.comps.base_type.to_inhibit]
        return merge_apat_list(
            [ActivityPattern(i.neurons,i.vals*0)
             for i in inhibit_apat_list])
        # base_apat = self.comps.base_type.getapat(network)
        # if self.comps.base_type.apat_mode == 'cont':
        #     return ActivityPattern(base_apat.neurons,
        #                            base_apat.vals*0)
        # else:
        #     return ActivityPattern([])

class BType(ttr.BTypeClass,Type):
    def __init__(self,name=gensym('BT'),nu=None):
        ttr.BTypeClass.__init__(self,name)
        self.fixed_nu = nu
        

class PType(ttr.PTypeClass,Type):
    def __init__(self,pred,args,nu=None):
        ttr.PTypeClass.__init__(self,pred,args)
        self.fixed_nu = nu
    def nu(self,assgn):
        if self.fixed_nu is None:
            res = PType_n(self.comps.pred,self.comps.args,assgn)
            res.name = show(self)+'_n'
            return res
    def subst(self,v,a):
        if self == v:
            return a
        else:
            newargs = []
            for arg in self.comps.args:
                if arg == v: newargs.append(a)
                elif isinstance(arg,str): newargs.append(arg)
                else: newargs.append(substitute(arg,v,a))      #arg.subst(v,a))
            return PType(self.comps.pred,newargs)



# class PType_n(Type_n,ttr.PType):
#     def __init__(self,pred,args):
#         ttr.PType.__init__(self,pred,args)
#     def add_apat(self,network,apat):
#         print(show(self)+' is a logical type and cannot add activity patterns.')
#     def getapat(self,network,assgn=None,io=iota):
#         if assgn is None:
#             assgn = {'in_use':[]}
#         return mkntype_ptype(self.comps.pred,self.comps.args,io,assgn,network).getapat(network)
#     def add_grandmother(self,network):
#         print(show(self)+' is a logical type and cannot add grandmothers.')

# def mkntype_ptype(pred,args,io,assgn,network):
#     arglabels = ['arg'+str(i) for i in range(len(pred.arity))]
#     argtypes = [MeetType_n(pred.nu.__getattribute__(arglabel),
#                            iota_assgn(arg,io,assgn,network))
#                 for arglabel,arg in zip(arglabels,args)]
#     types = []
#     for i in range(len(argtypes)):
#         if i is 0:
#             types.append(MeetType_n(pred.nu.pred,argtypes[0]))
#         else:
#             types.append(MeetType_n(InhibitType_n(argtypes[i-1]),argtypes[i]))
#     types.append(InhibitType_n(MeetType_n(pred.nu.pred,argtypes[-1])))
#     return StringType_n(types)
    
# def iota_assgn(arg,io,assgn,network):
#     if arg in assgn:
#         return assgn[arg]
#     elif isinstance(arg,str):
#         return io.gettype(arg,network)
#     else:
#         return arg.nu
    
class PType_n(ttr.PTypeClass,Type_n):
    def __init__(self,pred,args,assgn):
        ttr.PTypeClass.__init__(self,pred,args)
        self.to_inhibit = []
        self.assgn = assgn
    def add_apat(self,network,apat):
        print(show(self)+' is a logical type and cannot add activity patterns.')
    def getapat(self,network,gsym=gensym_n,io=iota):
        if self.assgn is None:
            self.assgn = {'in_use':[]}
        old_in_use = list(self.assgn['in_use'])
        res =  mkntype_ptype(self.comps.pred,self.comps.args,io,self.assgn,gsym,network).getapat(network)
        self.assgn['in_use'] = old_in_use
        return res
    def add_grandmother(self,network):
        print(show(self)+' is a logical type and cannot add grandmothers.')
    def judgmnt_type_n(self,objn,assgn=None):
        if self.comps.pred is orpred:
            T_n = MeetType_n(self,StringType_n([objn,InhibitType_n(objn)],assgn),assgn)
        else:
            T_n = MeetType_n(self,objn,assgn)
        return StringType_n([T_n,InhibitType_n(T_n)],assgn)

def mkntype_ptype(pred,args,io,assgn,gsym,network):
    T_ptype = Type_n(assgn=assgn)
    T_ptype.add_apat(network,ActivityPattern([[gsym.index('ptype'+str(len(pred.arity)),network,assgn)]]))
    T_rel = Type_n(assgn=assgn)
    T_rel.add_apat(network,ActivityPattern([[gsym.index('rel',network,assgn)]]))
    arglabels = ['arg'+str(i) for i in range(len(pred.arity))]

    argtypes = [Type_n(assgn=assgn) for l in arglabels]
    for T,l in zip(argtypes,arglabels):
        T.add_apat(network,ActivityPattern([[gsym.index(l,network,assgn)]]))
    # argtypes = [MeetType_n(pred.nu.__getattribute__(arglabel),
    #                        iota_assgn(arg,io,assgn))
    #             for arglabel,arg in zip(arglabels,args)]
    T_relpred = MeetType_n(T_rel,nu(pred,assgn),assgn)
    argtypesargs = [MeetType_n(T_arg,iota_assgn(arg,io,assgn),assgn) for T_arg,arg in zip(argtypes,args)]
    types = []
    types.append(MeetType_n(T_ptype,T_relpred,assgn))
    for i in range(len(argtypes)):
        if i == 0:
            types.append(MeetType_n(InhibitType_n(T_relpred),argtypesargs[0],assgn))
        else:
            types.append(MeetType_n(InhibitType_n(argtypesargs[i-1]),argtypesargs[i],assgn))
    types.append(InhibitType_n(MeetType_n(T_ptype,argtypesargs[-1],assgn)))
    return StringType_n(types,assgn)

def iota_assgn(arg,io,assgn):
    if hashable(arg) and arg in assgn:
        return assgn[arg]
    elif isinstance(arg,str):
        return io.gettype_n(arg)
    else:
        return nu(arg,assgn)

#Should be moved to utils
def hashable(obj):
    try:
        hash(obj)
        return True
    except TypeError:
        return False

class MeetType(ttr.MeetType,Type):
    def __init__(self,T1,T2,nu=None):
        ttr.MeetType.__init__(self,T1,T2)
        self.fixed_nu = nu
    def nu(self,assgn):
        if self.fixed_nu is None:
            res = PType_n(andpred,[self.comps.left,self.comps.right],assgn) # Meet types are treated neurologically as neurological PTypes not neurological Meet types
            res.name = show(self)+'_n'
            return res
        else:
            return self.fixed_nu
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return MeetType(self.comps.left.subst(v,a),self.comps.right.subst(v,a))

class JoinType(ttr.JoinType,Type):
    def __init__(self,T1,T2,nu=None):
        ttr.JoinType.__init__(self,T1,T2)
        self.fixed_nu = nu
    def nu(self,assgn):
        if self.fixed_nu is None:
            res = PType_n(orpred,[self.comps.left,self.comps.right],assgn) # Join types are treated neurologically as neurological PTypes not neurological Meet types
            res.name = show(self)+'_n'
            # def join_judgmnt_type_n(s,an):
            #     T1 = MeetType_n(or_n.nu.pred,Ta)
            #     T2 = MeetType_n(s,InhibitType_n(Ta))
            #     return StringType_n([T1,T2])
            # res.judgmnt_type_n = join_judgmnt_type_n.__get__(self.nu,self.nu.__class__)
            return res
        else:
            return self.fixed_nu
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return JoinType(self.comps.left.subst(v,a),self.comps.right.subst(v,a))

class MeetType_n(ttr.MeetType,Type_n):
    def __init__(self,T1,T2,assgn):
        ttr.MeetType.__init__(self,T1,T2)
        self.to_inhibit = T1.to_inhibit+T2.to_inhibit
        self.assgn = assgn
        # if T1.apat_mode == 'cont':
        #     self.apat_mode = 'cont'
        # elif T2.apat_mode == 'cont':
        #     self.apat_mode = 'cont'
        # else:
        #     self.apat_mode = 'spike'
        #self.apat_mode = 'cont'
    def add_apat(self,network,apat):
        print(show(self)+' is a logical type and cannot add activity patterns.')
    def getapat(self,network):
        return self.comps.left.getapat(network).merge(self.comps.right.getapat(network))
    def add_grandmother(self,network):
        print(show(self)+' is a logical type and cannot add grandmothers.')

class FunType(ttr.FunType,Type):
    def __init__(self,T1,T2):
        ttr.FunType.__init__(self,T1,T2)
    def subst(self,v,a):
        if self == v:
            return a
        else: return FunType(self.comps.domain.subst(v,a),self.comps.range.subst(v,a))

class RecType(ttr.RecType,Type):
    def __init__(self,d={}):
        ttr.RecType.__init__(self,d)
        self.comps = Rec(d)
    def nu(self,assgn):
        return RecType_n(self.comps.__dict__,assgn)
    def subst(self,v,a):
        res = RecType()
        # for l in self.comps.__dict__.keys():
        #     if self.comps.__getattribute__(l) == v:
        #         res.addfield(l,a)
        #     elif isinstance(self.comps.__getattribute__(l),str):
        #         res.addfield(l,self.comps.__getattribute__(l))
        #     else: 
        #         res.addfield(l,substitute(self.comps.__getattribute__(l),v,a))
        # #print(show(res))
        # return res
        res.comps = self.comps.subst(v,a)
        return res

class RecType_n(ttr.RecType,Type_n):
    def __init__(self,d={},assgn=None):
        ttr.RecType.__init__(self,d)
        self.comps = Rec(d)
        self.to_inhibit = []
        self.assgn = assgn
    def add_apat(self,network,apat):
        print(show(self)+' is a logical type and cannot add activity patterns.')
    def getapat(self,network):
        if self.assgn is None:
            self.assgn = {'in_use':[]}
        old_in_use = list(self.assgn['in_use'])
        res =  nu(self.comps,self.assgn).getapat(network)
        self.assgn['in_use'] = old_in_use
        return res
    def add_grandmother(self,network):
        print(show(self)+' is a logical type and cannot add grandmothers.')
    def resolve(self,recn):
        d={}
        for l in self.comps.__dict__:
            v=self.comps.__dict__.__getitem__(l)
            if isinstance(v,tuple):
                d.__setitem__(l,v[0].app_recursive([recn.rec.__dict__.__getitem__(a) for a in v[1]]))
            else:
                d.__setitem__(l,v)
        return RecType_n(d)
    def judgmnt_type_n(self,recn):
        resolved = self.resolve(recn)
        types = [nu(resolved.comps.__dict__.__getitem__(l),self.assgn)
                 .judgmnt_type_n(nu(recn.rec.__dict__.__getitem__(l),self.assgn))
                 for l in resolved.comps.__dict__]
        return StringType_n(types,self.assgn)

    

class StringType_n(ttr.TTRStringType,Type_n):
    def __init__(self,list,assgn):
        ttr.TTRStringType.__init__(self,list)
        self.to_inhibit = []
        self.assgn = assgn
    def add_apat(self,network,apat):
        print(show(self)+' is a logical type and cannot add activity patterns.')
    def getapat(self,network):
        # postypes = self.comps.types
        # negtypes = [InhibitType_n(i) for i in postypes]
        # types = [postypes[0]]+
        #     [i.merge(j) for i,j in zip(negtypes[:-1],postypes[1:])]+
        #         negtypes[-1]
        res = self.comps.types[0].getapat(network)
        for i in self.comps.types[1:]:
            res = res.concat(i.getapat(network))
        return res
    def add_grandmother(self,network):
        print(show(self)+' is a logical type and cannot add grandmothers.')







#===========================================================
# Types
#===========================================================

Ty = ttr.Ty

#===========================================================
# Non-type classes
#===========================================================

class Pred(ttr.Pred):
    def __init__(self,name,arity,nu=None):
        ttr.Pred.__init__(self,name,arity)
        self.fixed_nu = nu
    def nu(self,assgn):
        if self.fixed_nu is None:
            self.fixed_nu = Type_n(self.name+'_n')
        return self.fixed_nu
    # def add_grandmothers(self,network):
    #     self.nu.pred.add_grandmother(network)
    #     arg_labels = ['arg'+str(i) for i in range(len(self.nu.__dict__)-1)]
    #     for l in arg_labels:
    #         self.nu.__getattribute__(l).add_grandmother(network)
    
    
         # if self.nu == None:
        #     self.nu = rec.Rec({'pred':Type_n(self.name+'_n')})
        #     for i in range(len(arity)):
        #         self.nu.addfield('arg'+str(i),Type_n(self.name+'_arg'+str(i)))           

andpred = Pred('&',[Ty,Ty])
orpred = Pred('v',[Ty,Ty])
and_n = nu(andpred)
or_n = nu(orpred)




class DepType(ttr.Fun):
    def __init__(self,v,dom,body):
        ttr.Fun.__init__(self,v,dom,body)
    def nu(self,assgn):
        return DepType_n(self.var,self.domain_type,self.body,assgn)
    def subst(self,v,a):
        if self == v:
            return a
        else:
            return DepType(self.var,
                           substitute(self.domain_type,v,a),
                           substitute(self.body,v,a))
    def app_recursive(self,args):
        if args == []:
            return self
        else:
            res = self.app(args[0])
            if isinstance(res,DepType):
                return res.app_recursive(args[1:])
            else:
                return res

class DepType_n(ttr.Fun,Type_n):
    def __init__(self,v,dom,body,assgn=None):
        ttr.Fun.__init__(self,v,dom,body)
        self.to_inhibit = []
        self.assgn = assgn
    def add_apat(self,network,apat):
        print(show(self)+' is a logical type and cannot add activity patterns.')
    def getapat(self,network,gsym=gensym_n):
        if self.assgn is None:
            self.assgn = {'in_use':[]}
        old_in_use = list(self.assgn['in_use'])
        res =  mkntype_deptype(self.var,self.domain_type,
                               self.body,self.assgn,gsym,network).getapat(network)
        self.assgn['in_use'] = old_in_use
        return res
    def add_grandmother(self,network):
        print(show(self)+' is a logical type and cannot add grandmothers.')
    def apply_n(self,obj):
        return nu(self.app(obj))
        
def mkntype_deptype(var,domain_type,body,assgn,gsym,network):
    T_lam = Type_n(assgn=assgn)
    T_lam.add_apat(network,ActivityPattern([[gsym.index('lambda',network,assgn)]]))
    T_dom = Type_n(assgn=assgn)
    T_dom.add_apat(network,ActivityPattern([[gsym.index('dom',network,assgn)]]))
    T_var = Type_n(assgn=assgn)
    var_index = gsym.index('var',network,assgn)
    T_var.add_apat(network,ActivityPattern([[var_index]]))
    assgn[var] = T_var
    T_start = MeetType_n(MeetType_n(T_lam,T_dom,assgn),
                         MeetType_n(T_var,nu(domain_type,assgn),assgn),assgn)
    T_rng = Type_n(assgn=assgn)
    T_rng.add_apat(network,ActivityPattern([[gsym.index('rng',network,assgn)]]))
    T_body = Type_n(assgn=assgn)
    T_body.add_apat(network,nu(body,assgn).getapat(network))
    return StringType_n([T_start,
                         MeetType_n(InhibitType_n(MeetType_n(T_dom,
                                                             MeetType_n(T_var,
                                                                        nu(domain_type,assgn),assgn),assgn)),
                                    MeetType_n(T_rng,T_body,assgn),assgn),
                         InhibitType_n(MeetType_n(T_lam,
                                                  T_rng,assgn),assgn)
                         ],assgn)        


class Rec(rec.Rec):
    def __init__(self,d={}):
        rec.Rec.__init__(self,d)
        #recs[self] = Rec_n(d)
    def nu(self,assgn):
        return Rec_n(self.__dict__,assgn)
    def subst(self,v,a):
        res = Rec()
        for l in self.__dict__.keys():
            lval = self.__getattribute__(l)
            if lval == v:
                res.addfield(l,a)
            elif isinstance(lval,str):
                res.addfield(l,lval)
            else: 
                res.addfield(l,substitute(lval,v,a))
        recs[res] = Rec_n(res.__dict__)
        return res


class Rec_n(Type_n,rec.Rec):
    def __init__(self,d={},assgn=None):
        self.rec = rec.Rec(d)
        self.to_inhibit = []
        self.assgn = assgn
    def show(self):
        return self.rec.show()
    def getapat(self,network,gsym=gensym_n,io=iota):
        if self.assgn is None:
            self.assgn = {'in_use':[]}
        old_in_use = list(self.assgn['in_use'])
        postypes = []
        for fld in self.rec.__dict__.items():
            t = mkntype_field(fld,io,self.assgn,gsym,network)
            postypes.append(t)
        negtypes = [InhibitType_n(T,self.assgn) for T in postypes]
        T_rec = Type_n(assgn=self.assgn)
        T_rec.add_apat(network,ActivityPattern([[gsym.index('rec',network,self.assgn)]]))
        T_start = MeetType_n(T_rec,postypes[0],self.assgn)
        T_end = MeetType_n(InhibitType_n(T_rec),negtypes[-1],self.assgn)
        res = StringType_n([T_start]+
                            [MeetType_n(T1,T2,self.assgn)
                             for T1,T2 in zip(negtypes[:-1],postypes[1:])]+
                            [T_end],self.assgn
                            ).getapat(network)
        self.assgn['in_use'] = old_in_use
        return res


def mkntype_field(fld,io,assgn,gsym,network):
    #old_in_use = list(assgn['in_use'])
    T_field = Type_n(assgn=assgn)
    T_field.add_apat(network,ActivityPattern([[gsym.index('field',network,assgn)]]))
    T_label = Type_n(assgn=assgn)
    T_label.add_apat(network,ActivityPattern([[gsym.index('label',network,assgn)]]))
    T_field0 = labels.gettype_n(fld[0])
    T_label_field0 = MeetType_n(T_label,T_field0,assgn)
    T_value = Type_n(assgn=assgn)
    T_value.add_apat(network,ActivityPattern([[gsym.index('value',network,assgn)]]))
    T_field1 = iota_assgn(fld[1],io,assgn)
    T_value_field1 = MeetType_n(T_value,T_field1,assgn)
    res = StringType_n([MeetType_n(T_field,T_label_field0,assgn),
                        MeetType_n(InhibitType_n(T_label_field0,assgn),
                                   T_value_field1,assgn),
                        MeetType_n(InhibitType_n(T_value_field1,assgn),
                                   InhibitType_n(T_field,assgn),assgn)],assgn)
    #assgn['in_use'] = old_in_use
    return res
    

# def AusProp(obj,type):
#     return Rec({'l_type':type,'l_obj':obj})

# def AusProp_n(obj,type):
#     return Rec_n({'l_type':type,'l_obj':obj})
