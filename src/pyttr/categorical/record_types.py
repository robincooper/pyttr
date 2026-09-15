from ..core.model import _M
from ..core.records import Rec
from ..core.terms import HypObj
from ..core.type_core import TypeClass
from ..core.record_types import (RecTypeStructure, LabelsRecType, AttValRecType,
    ComputeDepType, CheckField, CheckPathList, CheckPath, ProcessDepFields)
from ..utils import forsome, forall
from .type_core import TypeClass as CategoricalType

class RecType(RecTypeStructure, CategoricalType):
    def __init__(self, d=None):
        super().__init__(d)
        self.witness_conditions = [lambda r: isinstance(r, Rec) and RecOfRecType(r, self, self.poss)]

    def in_poss(self, poss):
        self.poss = poss
        return self

    def create(self):
        return self._create_record()

    def create_hypobj(self):
        return self._create_record('hyp')

def RecOfRecType(r,T,M):
    TypeLabels = [l for l in T.comps]
    RecordLabels = [l for l in r]
    if forsome(TypeLabels, lambda l: l not in RecordLabels):
        return False
    elif forall(TypeLabels, lambda l: l in RecordLabels and QueryField(l,r,T,M)):
        return True
    else:
        return False

def QueryField(l,r,T,M):
    TInField = T.comps[l]
    Obj = r[l]
    if isinstance(Obj,HypObj):
        M = _M
    if isinstance(TInField, TypeClass):
        return TInField.in_poss(M).query(Obj) 
    else:
        TResolved = ComputeDepType(r,TInField,M)
        return TResolved.in_poss(M).query(Obj)

__all__ = ['RecType', 'LabelsRecType', 'AttValRecType', 'RecOfRecType', 'QueryField', 'ComputeDepType', 'CheckField', 'CheckPathList', 'CheckPath', 'ProcessDepFields']
