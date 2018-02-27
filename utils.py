from itertools import count
from IPython.display import Latex

gennum = dict()

def gensym(x):
    if x not in gennum:
        gennum[x] = count() 
    return x+'_{'+str(gennum[x].__next__())+'}'


def some_condition(conds,obj):
    if len(conds) == 0: return False
    elif conds[0](obj) == True: return True
    else: return some_condition(conds[1:],obj)

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
        

def to_latex(obj):
    if isinstance(obj,str):
        return '\\text{'+obj+'}'
    elif isinstance(obj,list):
        return '[ '+ ', '.join([to_latex(x) for x in obj])+']'
    elif isinstance(obj,tuple):
        return '\\langle '+ ', '.join([to_latex(x) for x in obj])+'\\rangle'
    elif isinstance(obj,dict):
        return '\\left\\{\\begin{array}{rcl}\n'+'\\\\\n'.join([to_latex(i[0])+' &=& '+to_latex(i[1]) for i in obj.items()])+'\n\\end{array}\\right\\}'
    elif 'to_latex' in dir(obj):
        return obj.to_latex()
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

def substitute(obj,v,a):
    if obj == v:
        return a
    elif isinstance(obj,list):
        return [substitute(x,v,a) for x in obj]
    elif isinstance(obj,tuple):
        return tuple((substitute(x,v,a) for x in obj))
    elif 'subst' in dir(obj):
        return obj.subst(v,a)
    else: 
        return obj

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
