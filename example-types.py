#sys.path.append('')

from ttrtypes import Type, BType, PType, Pred, MeetType, JoinType, ListType, \
SingletonType, HypObj, LazyObj, FunType, RecType, Fun, Ty, Re, RecTy, Possibility, AbsPath, TTRString, TTRStringType, KPlusStringType
from records import Rec
from utils import show, example, ttrace, nottrace, ttracing

Ind = BType('Ind')

Ind.judge('j')
Ind.judge('k')
Ind.judge('l')
Ind.judge('m')

print(Ind.judge('j'))

print(Ind.judge('n'))

print(Ind.witness_cache)

print(Ind.query('h'))

print(Ind.create())

run = Pred('run',[Ind])

p = PType(run,['j'])

print(show(p))

print(p.validate())

p.create()

print(p.witness_cache)

print(Ind.judge_nonspec())

print(p.query_nonspec())

print(p.judge_nonspec())

man = Pred('man',[Ind])

manj = PType(man,['j'])

manj.create()

print(manj.witness_cache)

T1 = Type()

T2 = Type()

T1.judge('a')

T2.judge('a')

T1.judge('b')

T = MeetType(T1,T2)


print(T.query('a'))

print(T.query('b'))

print(T.judge_nonspec())

T11 = Type()
T21 = Type()
T31 = MeetType(T11,T21)
print(T31.judge_nonspec())
print(T31.witness_cache)
print(T11.witness_cache)
print(T21.witness_cache)
print(T31.create())



T3 = JoinType(T1,T2)

print(T3.query('a'))

print(T3.query('b'))

print(T3.create())
print(T3.witness_cache)

x = HypObj([Ind])

print(show(x.types))

print(x.validate())

T4 = Type()

x1 = T4.create_hypobj()

print(show(x1.types))

x2 = T.create_hypobj()

print(show(x2.types))

print(T1.query(x2))

print(T1.subtype_of(T1))
print(T.subtype_of(T1))
print(T1.subtype_of(T3))
print(T3.subtype_of(T1))
print(T.subtype_of(T3))

ttrace()
T.learn_witness_condition(lambda x: x)
nottrace()

f = Fun('x',Ind,'x')
print(f.app('j'))
IndToInd = FunType(Ind,Ind)
print(IndToInd.query(f))
print(IndToInd.query_nonspec()) # Perhaps function types should be non-empty if their domain and range types are non-empty or if it's not the case that: the domain type is empty and the range type is non-empty (material conditional)
a = IndToInd.create_hypobj()
print(show(a))

print(f.validate_arg('j'))
print(f.validate_arg('x'))



f1 = Fun('x',Ind,PType(run,['x']))
print(f1.show())
p1 = f1.app('j')
print(show(p1))

p1c = f1.appc('j')
print(show(p1c))


ttrace()
print(show(f1.appc('x')))
nottrace()

print(Ty.query(T))
print(Ty.query(Ty))
print(Ty.query(p1))
print(Ty.query_nonspec()) # Presumably this should be True since at least Ty.query(Ty) returns True


ttrace()
Ty.learn_witness_condition(lambda x: x)
nottrace()

IndToTy = FunType(Ind,Ty)
print(IndToTy.query(f1))
print(IndToTy.query(f))

f2 = Fun('x',Ind,PType(man,['x']))
print(show(f2))

love = Pred('love',[Ind,Ind])
f3 = Fun('x',Ind,Fun('y',Ind,PType(love,['x','y'])))
p2 = f3.app('j').app('m')
print(show(p2))
p3 = Fun('x',Ind,Fun('y',Ind,PType(love,['x','y'])).app('j')).app('m')
print(show(p3))

ListInd = ListType(Ind)
print(ListInd.query(['j','k']))
print(show(ListInd))
print(ListInd.query([]))

Ind_j = SingletonType(Ind,'j')
print(Ind_j.query('j'))
print(Ind_j.query('k'))
print(Ind_j.query('x'))
print(show(Ind_j))


Ind_jk = SingletonType(ListType(Ind),['j']+['k'])
print(show(Ind_jk))
print(Ind_jk.query(['j','k']))

Ind_appk = SingletonType(Ind,Fun('x',Ind,'j').app('k'))
print(show(Ind_appk))
print(Ind_appk.query('j'))

print(Fun('x',Ind,Ind).app('j').query('k'))

print(Fun('x',Ind,PType(man,['x'])).app('j').query_nonspec())

print(show(Fun('x',Ind,PType(man,['x'])).app('j')))

print(show(manj))

print(manj.query_nonspec())

M = Possibility('M')
manj.in_poss(M)
print(Fun('x',Ind,PType(man,['x'])).app('j').in_poss(M).query_nonspec())

print(show(M))

print(Ty.query(RecType({'x':Ind})))

print(RecType({'x':Ind}).query(Rec({'x':'j'})))

print(RecType({'x':Ind}).query(Rec({'x':'j', 'y':'k','z':'e1'})))

print(RecType({'x':Ind, 'y':Ind}).query(Rec({'x':'j'}))) #False

print(RecTy.query(RecType({'x':Ind,
                           'c':(Fun('v',Ind,PType(man,['v'])), ['x'])})))

T_man = RecType({'x':Ind, 'c':(Fun('v',Ind,PType(man,['v'])), ['x'])})

print(T_man.query(Rec({'x':'j', 'c':'_e1'})))

Ind.in_poss(M)
T_man.in_poss(M)

print(show(M))

print(T_man.query(Rec({'x':'j', 'c':'_e1'})))

print(RecType({'x':Ind, \
               'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x'])})
      .in_poss(M)
      .query(Rec({'x':'j',
                  'y':'j',
                  'c':'e1'})))
               
print(show(T_man))

print(show(T_man.create())) 

print(show(M))

print(T_man.query(T_man.create()))

print(RecTy.query(RecType({'x':Ind,
                           'c': RecType({'c': (Fun('v',Ind,PType(man,['v'])), ['x'])})}))) #True, even though the path in the dependent field is not defined (too deeply embedded)

print(T_man.subtype_of(T_man))

print(RecType({'x':Ind,
               'c': (Fun('v',Ind,PType(man,['v'])), ['x'])}).subtype_of(Re))

print(RecType({'x':Ind,
               'c': RecType({'c': (Fun('v',Ind,PType(man,['v'])), ['x'])})})
      .subtype_of(Re))  #returns an error (but also True for some reason)

print(show(RecType({'x':Ind,
                    'c': RecType({'c': (Fun('v',Ind,PType(man,['v'])), ['x'])})})))

print(RecType({'x':Ind,
               'c': RecType({'c': (Fun('v',Ind,PType(man,['v'])), ['x'])})})
      .validate()) 
 # False.  This would have been True in the Oz implementation since
 # paths always started from the top of the record type.  Now paths
 # start in the record type in which they occur.

print(T_man.validate())

print(RecType({'x':Ind,
               'e':(Fun('v',Ind,RecType({'e':PType(man,['v'])})), ['x'])})
      .validate())
# True. Here the function is at the right level. 

print(RecType({'x':Ind,
               'e':(Fun('v',Ind,RecType({'e':PType(man,['v'])})), ['x'])})
      .in_poss(M)
      .query(Rec({'x':'j',
                  'y':'j',
                  'e':Rec({'e':'e1'})}))) # False. No 'y' in the type

print(RecType({'x':Ind,
               'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x'])})
      .in_poss(M)
      .query(Rec({'x':'j',
                  'y':'j',
                  'e':Rec({'e':'_e1'})})))

print(RecType({'x':Ind,
               'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x']),
               'e':(Fun('v',Ind,RecType({'e':PType(man,['v'])})), ['y'])})
      .in_poss(M).query(Rec({'x':'j',
                             'y':'j',
                             'e':Rec({'e':'_e1'})})))

print(show(RecType({'x':Ind,
                    'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x']),
                    'e':(Fun('v',Ind,RecType({'e':PType(man,['v'])})), ['y'])})
           .in_poss(M)
           .create()))



print(RecType({'x':Ind,
               'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x']),
               'e':(Fun('v',Ind,RecType({'e':PType(man,['v'])})), ['y'])})
      .in_poss(M)
      .judge(Rec({'x':'j',
                  'y':'j',
                  'e':Rec({'e':'_e1'})})))

T_a_man =  RecType({'x':Ind,
                    'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x']),
                    'e':(Fun('v',Ind,RecType({'e':PType(man,['v'])})), ['y'])})

T_a_man.in_poss(M).judge(Rec({'x':'j',
                              'y':'j',
                              'e':Rec({'e':'_e1'})}))

print(show(T_a_man.witness_cache))

print(RecType({'x':Ind,
               'y':Ind})
      .subtype_of(RecType({'x':Ind})))

print(RecType({'x':Ind,
               'y':Ind,
               'e': (Fun('v',Ind,PType(man,['v'])),['y'])})
      .subtype_of(RecType({'x':Ind,
                           'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x']),
                           'e': (Fun('v',Ind,PType(man,['v'])),['y'])}))) #False

print(RecType({'x':Ind,
               'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x']),
               'e': (Fun('v',Ind,PType(man,['v'])),['y'])})
      .subtype_of(RecType({'x':Ind,
                           'y':Ind,
                           'e': (Fun('v',Ind,PType(man,['v'])),['y'])})))
#True but returns an error



R1 = RecType({'x':Ind,
              'y':(Fun('v',Ind,SingletonType(Ind,'v')),['x']),
              'e': (Fun('v',Ind,PType(man,['v'])),['y'])})

R2 = RecType({'x':Ind,
              'y':Ind,
              'e': (Fun('v',Ind,PType(man,['v'])),['y'])})

print(R1.subtype_of(R2))

print(RecType({'x' : R1})
      .subtype_of(RecType({'x' : R2})))

print(RecTy.query(RecType({'x' : Ind,
                           'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})))

print(RecType({'x' : Ind,
               'e' : (Fun('v',Ind,PType(man,['v'])),['x'])}).validate())

print(RecTy.query(RecType({'x' : Ty,
                           'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})))
#In the earlier implementation this was false.  If we want to replicate this we can first validate as below.

print(RecType({'x' : Ty,
               'e' : (Fun('v',Ind,PType(man,['v'])),['x'])}).validate())

example(47)
ttrace()
h1 = RecType({'x' : Ty,
              'e' : (Fun('v',Ind,PType(man,['v'])),['x'])}).create_hypobj()
print(show(h1))
nottrace()

example(48)
print(RecType({'x' : RecType({'x' : Ind,
                              'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})}).
            validate())


example(49)
print(RecType({'x' : (Fun('v',Ind,RecType({'x' : Ind,
                                           'e' : PType(man,['v'])})),['x'])}).
            validate())


example(50)
print(show(RecType({'x' : RecType({'x' : Ind,
                                   'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})})
           .create()))

example(51)
print(show(RecTy.create()))

example(52)
T5 = RecTy.create()
print(RecTy.query(T5))



example(53)
print(RecType({'x' : RecType({'x' : Ind,\
                              'e' : (Fun('v',Ind,PType(man,['v'])),['y'])}),
                'y' : Ind}).
            validate()) #False


example(54)
print(RecType({'x' : (Fun('v',Ind,RecType({'x' : Ind,
                                           'e' : PType(man,['v'])})),['y']),
               'y' : Ind}).
            validate())


example(55)
print(show(RecType({'x' : (Fun('v',Ind,RecType({'x' : Ind,
                                           'e' : PType(man,['v'])})),['y']),
               'y' : Ind}).
            create()))




example(56)
print(show(RecType({'x' : (Fun('v',Ind,RecType({'x' : Ind,
                                                'e' : PType(man,['v'])})),['y']),
                    'y' : Ind}).
            create_hypobj()))


example(57)
print(RecType({'x' : RecType({'x' : Ind,
                              'e' : (Fun('v',Ind,PType(man,['v'])),['x'])}),
               'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x.x'])}).
            validate()) 




example(58)
print(RecType({'x' : (Fun('v',Ind,RecType({'x' : Ind,
                                           'e' : PType(man,['v'])})),['y']),
               'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x.x'])}).
            validate())
# The corresponding type in the previous implementation would have
# been ok since it would have been written (mutatis mutandis)
# RecType({'x' : RecType({'x' : Ind,\
#                         'e' : (Fun('v',Ind, PType(man,['v'])),['y'])}),\
#          'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x.x'])})
# and path names in the dependent fields would always have been
# interpreted from the top of the record.  So this type from the old
# system is not expressible if path names are interpreted locally.
# However, there is a type very like it in (59) and (60):

example(59)
print(RecType({'x' : (Fun('v',Ind,RecType({'x' : SingletonType(Ind,'v'),
                                           'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})), ['y']),
               'y' : Ind}).
            validate())

example(60)
print(show(RecType({'x' : (Fun('v',Ind,RecType({'x' : SingletonType(Ind,'v'),
                                                'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})), ['y']),
               'y' : Ind}).
            create()))

print(show(RecType({'x' : (Fun('v',Ind,RecType({'x' : SingletonType(Ind,'v'),
                                                'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})), ['y']),
               'y' : Ind}).
            create_hypobj()))

example(61)
print(RecType({'x' : (Fun('v',Ind,RecType({'x' : SingletonType(Ind,'v'),\
                                     'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})), ['y']),
               'y' : Ind}).subtype_of(
RecType({'x' : RecType({'x' : Ind,
                        'e' : (Fun('v',Ind,PType(man,['v'])),['x'])}),
               'y' : Ind})
))

example(62)
#reverse of (61) -- false
print(
RecType({'x' : RecType({'x' : Ind,
                        'e' : (Fun('v',Ind,PType(man,['v'])),['x'])}),
         'y' : Ind}).subtype_of(
RecType({'x' : (Fun('v',Ind,RecType({'x' : SingletonType(Ind,'v'),
                                     'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})), ['y']),
         'y' : Ind})
))

example(63)
print(
RecType({'x' : (Fun('v',Ind,SingletonType(Ind,'v')),['y']),\
         'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x'])}).\
validate()
) #False

example(64)
ttrace()
print(
RecType({'x' : (Fun('v',Ind,SingletonType(Ind,'v')),['y']),
         'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x'])}).
create()
) #None
nottrace()

example(65)
ttrace()
print(
RecType({'x' : (Fun('v',Ind,SingletonType(Ind,'v')),['y']),
         'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x'])}).
create_hypobj()\
) #None
nottrace()

example(66)
print(\
RecType({'x' : (Fun('v',Ind,SingletonType(Ind,'v')),['y']),
         'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x'])}).
query(\
Rec({'x' : 'j',\
     'y' : 'j'})\
)\
) # True!

example(67)
print(\
RecType({'x' : (Fun('v',Ind,SingletonType(Ind,'v')),['y']),
         'y' : (Fun('v',Ind,SingletonType(Ind,'v')),['x'])}).
query(
Rec({'x' : 'j',
     'y' : 'k'})
)
) # False

# Examples (63)-(67) show that circularity in dependencies can be used
# in a limited fashion if desired.  Given a record that you are
# checking it is possible for the dependencies to be resolved using
# the record.  However, the type will not be validated and it is not
# possible to create objects of the type, which in turn means that it
# will not be possible to show that it is a subtype of another type.

example(68)
print(
RecType({'x' : ListType(Ind),
         'y' : ListType(Ind),
         'z' : (Fun('v1',ListType(Ind),
                Fun('v2',ListType(Ind),SingletonType(ListType(Ind),LazyObj(['v1','+','v2'])))),['x','y'])}).
validate()
) 

example(69)
print(
RecType({'x' : Ind,
         'y' : Ind,
         'e' : (Fun('v1',Ind,
                 Fun('v2',Ind,PType(love,['v1','v2']))), ['x','y'])}).
validate()
)

example(70)
PType(love,['j','m']).in_poss(M).judge('e8')
print(
RecType({'x' : Ind,
         'y' : Ind,
         'e' : (Fun('v1',Ind,
                 Fun('v2',Ind,PType(love,['v1','v2']))), ['x','y'])}).
in_poss(M).
query(Rec({'x' : 'j',
       'y' : 'm',
       'e' : 'e8'}))
)

example(71)
print(
RecType({'x' : ListType(Ind),
         'y' : ListType(Ind),
         'z' : (Fun('v1',ListType(Ind),
                Fun('v2',ListType(Ind),SingletonType(ListType(Ind),LazyObj(['v1','+','v2'])))),['x','y'])}).
query(
Rec({'x' : ['j'],
     'y' : ['m'],
     'z' : ['j', 'm']})
)
) 


example(72)
print(
show(
RecType({'x' : ListType(Ind),
         'y' : ListType(Ind),
         'z' : (Fun('v1',ListType(Ind),
                Fun('v2',ListType(Ind),SingletonType(ListType(Ind),LazyObj(['v1','+','v2'])))),['x','y'])}).
create_hypobj()
)
)

example(73)
print(
show(
RecType({'x' : SingletonType(ListType(Ind),['j']),
         'y' : ListType(Ind),
         'z' : (Fun('v1',ListType(Ind),
                Fun('v2',ListType(Ind),SingletonType(ListType(Ind),LazyObj(['v1','+','v2'])))),['x','y'])}).
create_hypobj()
)
)

example(74)
print(
show(
RecType({'x' : SingletonType(ListType(Ind),['j']),
         'y' : SingletonType(ListType(Ind),['m']),
         'z' : (Fun('v1',ListType(Ind),
                Fun('v2',ListType(Ind),SingletonType(ListType(Ind),LazyObj(['v1','+','v2'])))),['x','y'])}).
create_hypobj()
)
)

example(75)
print(
show(
RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','y'])}).
query(
Rec({'x' : Fun('v',Ind,RecType({'e' : PType(man, ['v'])})),
     'y' : 'j',
     'z' : RecType({'e' : PType(man, ['j'])})})
)
)
)


example(76)
print(
show(
RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'w' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','y'])}).
subtype_of(
RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'w' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','w'])})
)
)
) # False

example(77)
print(
show(
RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'w' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','y'])}).
create_hypobj(
)
)
)

example(78)
print(
show(
RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'w' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','y'])
         })
)
)

example(79)
print(
    show(
RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'w' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','y'])
         }).
subtype_of(RecType({'z' : RecTy}))
)
)


example(80)
print(
    show(
RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'w' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','y'])
         }).
         create_hypobj()
         )
         )

example(81)
print(
    show(
        RecType({'x' : FunType(Ind,RecTy),
         'y' : Ind,
         'w' : Ind,
         'z' : (Fun('f',FunType(Ind,RecTy), Fun('v',Ind,SingletonType(RecTy,LazyObj(['f','@','v'])))),
                 ['x','y'])
         }).
         subtype_of(RecType({'z' : RecTy}))
         )
         )

example(82)
TT1 = FunType(Ind, RecTy)
TT2 = FunType(Ind, Ty)
TT3 = FunType(TT1, TT2)
ff = Fun('f', TT1, Fun('x', Ind, LazyObj(['f','@','x'])))
print(TT3.query(ff))

example(83)
print(
Ty.query(RecType({'c' : (Fun('v', Ind, PType(man,['v'])),
                       [AbsPath(Rec({'x' : 'j'}), 'x')])}))
                       )

example(84)
TxInd = RecType({'x' : Ind})
print(
    FunType(TxInd, RecTy).
    query(Fun('r', TxInd, RecType({'c' : (Fun('v', Ind, PType(man,['v'])),
                        [AbsPath('r', 'x')])})))
                       )

example(85)
print(
    show(
        Fun('r', TxInd, RecType({'c' : (Fun('v', Ind, PType(man,['v'])),
                            [AbsPath('r', 'x')])})).app(Rec({'x' : 'j'}))
                        ))
                        


example(86)
print(
    show(
        RecType({'x' : Ind,
                 'y' : Ind})
        .merge(RecType({'x':Ind}))
        )
        )

example(87)
print(
    show(
     RecType({'x':Ind}).
     merge(RecType({'x' : Ind,
                    'y' : Ind}))
                    )
                    )

example(88)
print(
    show(
        JoinType(Ind,Ty).merge(RecTy)))

example(89)
print(
    show(
        JoinType(Ind,Ty).merge(Ind)
    )
    )

example(90)
print(
    show(
        JoinType(Ind,Ty).merge(JoinType(Ind,RecTy))
        )
        )

example(91)
print(
    show(
        Ind.merge(JoinType(Ind,Ty))
        ))

example(92)
print(
    show(
        RecType({'a' : Ind}).merge(RecType({'b' : Ind}))
        )
        )

example(93)
print(
    show(
        RecType({'a' : Ind,
                 'c' : JoinType(Ind,Ty)}).merge(RecType({'b' : Ind,
                                                         'c' : Ind}))
                                                         )
                                                         )

example(94)
T1 = RecType({'x' : Ind,
              'y' : (Fun('v', Ind, RecType({'a' : Ind,
                                            'c' : PType(man, ['v'])})), ['x']),
              'z' : Ind})
T2 = RecType({'x' : Ind,
              'y' : (Fun('v', Ind, RecType({'a' : Ind,
                                            'c' : PType(man, ['v'])})), ['x']),
              'w' : Ind})
print(
    show(
        T1.merge(T2)
        )
        )

example(95)
T1 = RecType({'x' : Ind,
              'y' : (Fun('v', Ind, RecType({'a' : Ind,
                                            'c' : PType(man, ['v'])})), ['x']),
              'z' : Ind})
T2 = RecType({'x' : Ind,
              'y' : (Fun('v', Ind, RecType({'a' : Ind,
                                            'c' : PType(man, ['v'])})), ['z']),
              'z' : Ind})
print(
    show(
        T1.merge(T2)
        )
        )

example(96)
T1 = RecType({'x' : SingletonType(Ind, 'j'),
              'y' : (Fun('v', Ind, RecType({'a' : Ind,
                                            'c' : PType(man, ['v'])})), ['x']),
              'z' : Ind})
T2 = RecType({'x' : Ind,
              'y' : (Fun('v', Ind, RecType({'a' : Ind,
                                            'c' : PType(man, ['v'])})), ['z']),
              'z' : SingletonType(Ind, 'j')})
print(
    show(
        T1.merge(T2)
        )
        )                                                              
# In the previous Oz implementation there was an operation that would simplify
# dependent types when the path associated with them pointed to a singleton
# type.  Not (yet) implemented here.

example(97)
T1 = RecType({'a' : Ind,
              'b' : Ind})
T2 = RecType({'a' : SingletonType(Ind, 'j')})
print(
    show(
        T1.merge(T2)
        )
        )

example(98)
T1 = Re
T2 = RecType({'a' : Ind})
print(
    show(
        T1.merge(T2)
        )
        )

example(99)
T1 = RecType({'a' : PType(man, ['j'])})
T2 = RecType({'a' : PType(man, ['m'])})
print(
    show(
        T1.merge(T2)
        )
        )
                                                        
example(100)
T1 = RecType({'x' : Ind,
              'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})
T2 = RecType({'e' : PType(man,['j'])})
print(
    show(
        T1.merge(T2)
        )
        )
print(
    show(
        T2.merge(T1)
        )
        )

example(101)
T1 = Ind
T2 = RecTy
print(
    show(
        T1.amerge(T2)
        )
        )


example(102)
T1 = RecType({'agenda' : SingletonType(ListType(Ty), [RecType({'e' : PType(run,['j'])})]),
              'latest_move' : SingletonType(ListType(Re),[])})
T2 = RecType({'agenda' : SingletonType(ListType(Ty),[]),
              'latest_move' : RecType({'e' : PType(run,['j'])})})
print(
    show(
        T1.amerge(T2)
        )
        )             

example(103)
T1 = RecType({'x' : Ind,
              'agenda' : (Fun('v',Ind,SingletonType(ListType(Ty), [RecType({'e' : PType(run,['v'])})])),['x']),
              'latest_move' : SingletonType(ListType(Re),[])})
T2 = RecType({'x' : Ind,
              'agenda' : SingletonType(ListType(Ty),[]),
              'latest_move' : (Fun('v',Ind,RecType({'e' : PType(run,['v'])})),['x'])})
print(
    show(
        T1.amerge(T2)
        )
        )

example(104)
T1 = RecType({'x' : Ind,
              'e' : (Fun('v',Ind,PType(run,['v'])),['x'])})
T2 = RecType({'x' : Ind,
              'e' : (Fun('v',Ind,PType(man,['v'])),['x'])})
print(
    show(
        T1.merge(T2)
        )
        )
print(
    show(
        T1.amerge(T2)
        )
        )

example(105)
T1 = RecType({'x' : Ind,
              'e' : (Fun('v',Ind,PType(run,['v'])),['x'])})
T2 = RecType({'y' : Ind,
              'e' : (Fun('v',Ind,PType(man,['v'])),['y'])})
print(
    show(
        T1.merge(T2)
        )
        )
print(
    show(
        T1.amerge(T2)
        )
        )

example(106)
T1 = RecType({'x' : Ind,
              'e' : (Fun('v',Ind,RecType({'y' : Ind,
                                          'e' : PType(run,['v'])})),['x'])})
T2 = RecType({'y' : Ind,
              'e' : (Fun('v',Ind,PType(man,['v'])),['y'])})
print(
    show(
        T1.merge(T2)
        )
        )
print(
    show(
        T1.amerge(T2)
        )
        )


example(107)
T1 = RecType({'x' : Ind,
              'e' : (Fun('v',Ind,RecType({'y' : Ind,
                                          'e' : PType(run,['v'])})),['x'])})
T2 = RecType({'y' : Ind,
              'e' : (Fun('v',Ind,RecType({'x' : Ind,
                                          'e' : PType(man,['v'])})),['y'])})
print(
    show(
        T1.merge(T2)
        )
        )
print(
    show(
        T1.amerge(T2)
        )
        )

example(108)
s = TTRString(['e1','e2'])
print(show(s))


example(109)
T = TTRStringType([PType(run,['j']),PType(run,['m'])])
print(show(T))
print(T.validate())
ttrace()
print(show(T.learn_witness_condition(lambda x: x)))
nottrace()
print(show(T.create()))
print(show(T.create_hypobj()))

example(110)
T = KPlusStringType(RecTy)
print(show(T))
print(
    show(
        T.query(TTRString([RecType({'e' : PType(run,['j'])}),
                           RecType({'e' : PType(run,['m'])})]))
        )
    )
print(T.validate())
ttrace()
print(show(T.learn_witness_condition(lambda x: x)))
nottrace()
print(show(T.create()))
print(show(T.create_hypobj()))

example(111)
T1 = TTRStringType([Re,Re])
T2 = KPlusStringType(Re)
print(show(T1.subtype_of(T2)))
print(show(T2.subtype_of(T1)))

example(112)
T1 = TTRStringType([Re,Re])
T2 = TTRStringType([RecType({'x' : Ind}), RecType({'y' : Ind})])
print(show(T1.subtype_of(T2)))
print(show(T2.subtype_of(T1)))

example(113)
T1 = KPlusStringType(Re)
T2 = TTRStringType([RecType({'x' : Ind}), RecType({'y' : Ind})])
print(show(T1.subtype_of(T2)))
print(show(T2.subtype_of(T1)))

example(114)
f = Fun('v',Ty,TTRStringType([RecType({'x' : 'v'}), RecType({'y' : 'v'})]))
print(show(f.app(Ind)))

example(115)
f = Fun('v',Ty,KPlusStringType(RecType({'x' : 'v'})))
print(show(f.app(Ind)))

example(116)
T1 = TTRStringType([RecType({'x' : Ind}), Re])
T2 = TTRStringType([Re, RecType({'y' : Ind})])
print(show(T1.merge(T2)))
print(show(T1.amerge(T2)))

example(117)
T1 = TTRStringType([RecType({'x' : Ind}), RecType({'x' : Ind})])
T2 = TTRStringType([Re, RecType({'x' : Ty})])
print(show(T1.merge(T2)))
print(show(T1.amerge(T2)))

example(118)
T1 = KPlusStringType(RecType({'x':Ind}))
T2 = KPlusStringType(Re)
print(show(T1.merge(T2)))
print(show(T1.amerge(T2)))

example(119)
T1 = KPlusStringType(RecType({'x':Ind}))
T2 = KPlusStringType(Ty)
print(show(T1.merge(T2)))
print(show(T1.amerge(T2)))

example(120)
T1 = TTRStringType([RecType({'x' : Ind}), RecType({'x' : Ind})])
T2 = KPlusStringType(RecType({'x':Ind}))
print(show(T1.merge(T2)))
print(show(T1.amerge(T2)))

example(121)
T1 = TTRStringType([RecType({'x' : Ind}), RecType({'x' : Ind})])
T2 = KPlusStringType(Ty)
print(show(T1.merge(T2)))
print(show(T1.amerge(T2)))


