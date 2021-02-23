from itertools import count
from IPython.display import Latex
import re
import inspect

gennum = dict()

def gensym(x):
    if x not in gennum:
        gennum[x] = count() 
    #return x+'_{'+str(gennum[x].__next__())+'}'
    return x+str(gennum[x].__next__())

# def some_condition(conds,obj,L):
#     res = some_condition1(conds,obj,L)
#     if 'loop_found' in L:
#         res = False
#     if len(list(filter(lambda x: x is 'query',[x[3] for x in inspect.stack()])))==1:
#         L.clear()
#     return res
    
    

def some_condition(conds,obj):
    if len(conds) == 0:
        return False
    else:
        if conds[0](obj) == True:
            return True
        else:
            return some_condition(conds[1:],obj)

def check_stack(f,args):
    frames = filter(lambda x: x[3] == f and list(inspect.getargvalues(x[0]).locals.values())[:len(args)] == args,
                   inspect.stack())
    next(frames,None)
    if next(frames,None):
        return True
                   



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
    
def show(obj):
    if isinstance(obj,str):
        return obj
    elif isinstance(obj,list):
        return '['+ ', '.join([show(x) for x in obj])+']'
    elif isinstance(obj,tuple):
        return '('+ ', '.join([show(x) for x in obj])+')'
    elif isinstance(obj,dict):
        return '{'+', '.join([show(i[0])+' = '+show(i[1]) for i in obj.items()])+'}'
    elif 'show' in dir(obj):
        return obj.show()
    else:
        return str(obj)
        

def to_latex(obj,vars=[],italic=[],anglebrackets=[]):
    if isinstance(obj,str):
        subscript = re.search('\d+$',obj)
        if not subscript:
            subscript = re.search('_\D+$',obj)
        if subscript:
            start = subscript.start()
            if obj in vars:
                return obj[:start]+'_{'+obj[start:]+'}'
            else:
                if italic:
                    return '\\textit{'+obj[:start]+'}_{\\textit{'+obj[start:].replace('_','')+'}}'
                else:
                    return '\\text{'+obj[:start]+'}_{\\text{'+obj[start:].replace('_','')+'}}'
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
           return '\\langle '+ ', '.join([to_latex(x,vars) for x in obj])+'\\rangle'
        else:
           return '[ '+ ', '.join([to_latex(x,vars) for x in obj])+']'
    elif isinstance(obj,tuple):
        return '\\langle '+ ', '.join([to_latex(x,vars,italic,anglebrackets) for x in obj])+'\\rangle'
    elif isinstance(obj,dict):
        return '\\left\\{\\begin{array}{rcl}\n'+'\\\\\n'.join([to_latex(i[0],vars)+' &=& '+to_latex(i[1],vars) for i in obj.items()])+'\n\\end{array}\\right\\}'
    elif 'to_latex' in dir(obj):
        return obj.to_latex(vars)
    else:
        return str(obj)

def to_ipython_latex(obj):
    return '\\begin{equation}'+ to_latex(obj) + '\\end{equation}'

def print_latex(obj):
    return print(to_ipython_latex(obj))

# ttrmacros = '\newcommand{\record}[1]{$\left[\mbox{\begin{tabular}{lcl} #1 \end{tabular}}\right]$} \n \
# \newcommand{\smallrecord}[1]{$\left[\mbox{\begin{tabular}{@{}l@{}c@{}l@{}} #1 \n \
# \end{tabular}}\right]$} \n \
# \n \
# \newcommand{\field}[2]{#1 & = & #2} \n \
# \newcommand{\tfield}[2]{#1 & : & #2} \n \
# \newcommand{\smalltfield}[2]{#1:#2 & &} \n \
# \newcommand{\mfield}[3]{#1=#2 & : & #3} \n \
# \newcommand{\smallmfield}[3]{#1=#2:#3 & &} \n \
# \newcommand{\rfield}[3]{#1$\underline{\varepsilon}$#2 & : & #3} \n \
# \newcommand{\smallrfield}[3]{#1$\underline{\varepsilon}$#2:#3 & &} \n \
# \newcommand{\hfield}[2]{{\sc #1} & & #2} \n'


def show_latex(obj):
    return Latex(to_ipython_latex(obj))
        
def showall(objs):
    return [show(obj) for obj in objs]

# def substitute(obj,v,a):
#     if obj == v:
#         return a
#     elif isinstance(obj,list):
#         return [substitute(x,v,a) for x in obj]
#     elif isinstance(obj,tuple):
#         return tuple((substitute(x,v,a) for x in obj))
#     elif 'subst' in dir(obj):
#         return obj.subst(v,a)
#     else: 
#         return obj

def substitute(obj,v,a):
    if obj == v:
        res = a
    elif isinstance(obj,list):
        res = [substitute(x,v,a) for x in obj]
    elif isinstance(obj,tuple):
        res = tuple((substitute(x,v,a) for x in obj))
    elif 'subst' in dir(obj):
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
    elif s in ttracing:
        ttracing_list.remove(s)
    else: pass
    return ttracing_list

def ttracing(s):
    global ttracing_list
    if s in ttracing_list:
        return True
    else:
        return False
