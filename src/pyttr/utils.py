from itertools import count
import re
import inspect
import warnings

try:
    from IPython.display import Latex
except ImportError:
    Latex = None

gennum = {}

def gensym(x):
    if x not in gennum:
        gennum[x] = count() 
    return x+str(gennum[x].__next__())

def some_condition(conds,obj):
    if len(conds) == 0:
        return False
    else:
        if conds[0](obj) == True:
             return True
        else:
            return some_condition(conds[1:],obj)


def check_stack(f,argsd):
    frames = filter(lambda x: x[3] == f and subdict(argsd,inspect.getargvalues(x[0]).locals),
                    inspect.stack())
    next(frames,None)
    if next(frames,None):
        return True
                   
def subdict(d1,d2):
    return forall([k for k in d1], lambda key: key in d2 and d1[key] == d2[key])

def apply123(f,x,y,z):
    n = f.__code__.co_argcount
    if n == 1:
        return f(x)
    elif n == 2:
        return f(x,y)
    else:
        return f(x,y,z)

def forall(list,cond):
    if list == []: return True
    elif cond(list[0]) == True: return forall(list[1:],cond)
    else: return False

def forsome(list,cond):
    if list == []: return False
    elif cond(list[0]) == True: 
        return True
    else:
        return forsome(list[1:],cond)
    
def _validate_max_record_depth(max_record_depth):
    if max_record_depth is not None and (
        not isinstance(max_record_depth, int) or max_record_depth < 0
    ):
        raise ValueError("max_record_depth must be a non-negative integer or None")


def show(obj, max_record_depth=None):
    """Render an object, optionally folding records beyond a nesting depth."""
    _validate_max_record_depth(max_record_depth)
    return _show(obj, max_record_depth, 0)


def _show(obj, max_record_depth, record_depth):
    if isinstance(obj,str):
        return obj
    elif isinstance(obj,list):
        return '['+ ', '.join([_show(x, max_record_depth, record_depth) for x in obj])+']'
    elif isinstance(obj,set):
        return '{'+ ', '.join([_show(x, max_record_depth, record_depth) for x in obj])+'}'
    elif isinstance(obj,tuple):
        return '('+ ', '.join([_show(x, max_record_depth, record_depth) for x in obj])+')'
    elif isinstance(obj,dict):
        return '{'+', '.join([
            _show(i[0], max_record_depth, record_depth)+' = '
            +_show(i[1], max_record_depth, record_depth)
            for i in obj.items()
        ])+'}'
    elif hasattr(obj, '_show'):
        return obj._show(max_record_depth, record_depth)
    elif hasattr(obj, 'show'):
        return obj.show()
    else:
        return str(obj)
        

def to_latex(obj,vars=None,italic=None,anglebrackets=None,max_record_depth=None):
    """Render LaTeX, optionally folding records beyond a nesting depth."""
    if vars is None:
        vars = []
    _validate_max_record_depth(max_record_depth)
    return _to_latex(
        obj, vars, italic, anglebrackets, max_record_depth, 0
    )


def _to_latex(obj,vars,italic,anglebrackets,max_record_depth,record_depth):
    if isinstance(obj,str):
        # Match an underscore-prefixed numeric suffix before a bare numeric
        # suffix, so ``c_1`` becomes ``c_{1}`` rather than ``c__{1}``.
        subscript = re.search(r'_\d+$',obj)
        if not subscript:
            subscript = re.search(r'\d+$',obj)
        if not subscript:
            subscript = re.search(r'_\D+$',obj)
        if subscript:
            start = subscript.start()
            base = obj[:start]
            suffix = obj[start:].removeprefix('_')
            if obj in vars:
                return base+'_{'+suffix+'}'
            else:
                if italic:
                    return '\\textit{'+base+'}_{\\textit{'+suffix+'}}'
                else:
                    return '\\text{'+base+'}_{\\text{'+suffix+'}}'
        else:
            if obj in vars:
                return obj
            else:
                if italic:
                    return '\\textit{'+obj+'}'
                else:
                    return '\\text{'+obj+'}'
    elif isinstance(obj,list):
        if anglebrackets:
           return '\\langle '+ ', '.join([
               _to_latex(x, vars, None, None, max_record_depth, record_depth)
               for x in obj
           ])+'\\rangle'
        else:
           return '[ '+ ', '.join([
               _to_latex(x, vars, None, None, max_record_depth, record_depth)
               for x in obj
           ])+']'
    elif isinstance(obj,tuple):
        return '\\langle '+ ', '.join([
            _to_latex(
                x, vars, italic, anglebrackets, max_record_depth, record_depth
            )
            for x in obj
        ])+'\\rangle'
    elif isinstance(obj,dict):
        return '\\left\\{\\begin{array}{rcl}\n'+'\\\\\n'.join([
            _to_latex(i[0], vars, None, None, max_record_depth, record_depth)
            +' &=& '
            +_to_latex(i[1], vars, None, None, max_record_depth, record_depth)
            for i in obj.items()
        ])+'\n\\end{array}\\right\\}'
    elif hasattr(obj, '_to_latex'):
        return obj._to_latex(vars, max_record_depth, record_depth)
    elif hasattr(obj, 'to_latex'):
        return obj.to_latex(vars)
    else:
        return str(obj)

def to_ipython_latex(obj):
    return '\\begin{equation}'+ to_latex(obj) + '\\end{equation}'

def print_latex(obj):
    return print(to_ipython_latex(obj))

def show_latex(obj):
    if Latex is None:
        raise RuntimeError('IPython is required for show_latex()')
    return Latex(to_ipython_latex(obj))
        
def showall(objs):
    return [show(obj) for obj in objs]

def substitute(obj,v,a):
    if obj == v:
        res = a
    elif isinstance(obj,list):
        res = [substitute(x,v,a) for x in obj]
    elif isinstance(obj,tuple):
        res = tuple((substitute(x,v,a) for x in obj))
    elif hasattr(obj, 'subst'):
        res =  obj.subst(v,a)
    else: 
        res = obj
    if res is obj:
        return obj
    elif show(res) == show(obj):
        return obj
    else:
        return res

def example(num):
    print('\n\nExample '+str(num)+':\n')



######################

# Tracing

######################

ttracing_list = list()

def ttrace(s='all'):
    global ttracing_list
    if s in ttracing_list:
        pass
    elif s=='all':
        ttracing_list.clear()
        ttracing_list += ['learn_witness_condition',
                          'pathvalue',
                          'create',
                          'create_hypobj',
                          'appc',
                          'appc_m',
                          'merge_dep_types',
                          'combine_dep_types',
                          'subtype_of_dep_types',
                          'ti_apply']
    else: ttracing_list.append(s)
    return ttracing_list

def nottrace(s='all'):
    global ttracing_list
    if s == 'all':
        ttracing_list.clear()
    elif s in ttracing_list:
        ttracing_list.remove(s)
    return ttracing_list

def ttracing(s):
    global ttracing_list
    if s in ttracing_list:
        return True
    else:
        return False

def trace(s, *values, **kwargs):
    if ttracing(s):
        print(*values, **kwargs)

def trace_any(channels, *values, **kwargs):
    if any(ttracing(s) for s in channels):
        print(*values, **kwargs)

def warn(message, category=UserWarning):
    warnings.warn(message, category, stacklevel=2)
