# -*- coding: utf-8 -*-
"""
Created on Tue Mar  3 15:05:58 2015

@author: cooper
"""

from records import Rec
from utils import show
r = Rec({'f':{'f':{'ff':'a', 'gg':'b'}, 'g':'c'}, 'g':{'h':{'g':'a','h':'d'}}})


print(show(r))
print(show(r.f))
print(show(r.g.h))
print(show(r.f.f.ff))

print(show(r.subst('a','z')))

print(show(r.flatten()))

print(show(r.flatten().unflatten()))

print(show(r.relabel('f','z')))

print(show(r.flatten().relabel("f.f.gg", "x.a")))

print(show(r.flatten().relabel("f.f.gg", "x.a").unflatten()))
