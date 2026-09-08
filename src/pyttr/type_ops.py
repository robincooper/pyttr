from .type_core import TypeClass
from .terms import Fun
from .utils import gensym, show, ttracing

def equal(x,y):
    # if show(x) == show(y):
    #     return True
    # else:
    #     return False
    if hasattr(x, 'poss') and hasattr(y, 'poss'):
        return x.poss == y.poss and show(x) == show(y)
    else:
        return show(x) == show(y)


def ti_apply(Tf, Targ):
    from .compound_types import FunType

    if isinstance(Tf, FunType) \
        and Targ.subtype_of(Tf.comps.domain):
        return Tf.comps.range
    else:
        if ttracing('ti_apply'):
            print('Not a well-typed function application: '+ show(Tf) + show(Targ))
        return None


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


__all__ = [
    "equal",
    "ti_apply",
    "merge_dep_types",
    "combine_dep_types",
    "subtype_of_dep_types",
]
