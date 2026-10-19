from pyttr.categorical.compound_types import SingletonType
from pyttr.categorical.record_types import RecType
from pyttr.categorical.type_core import BType


Cat = BType("Cat")
Cats = ["s", "np", "vp"]

for category in Cats:
    Cat.judge(category)


RuleID = BType("RuleID")


def valid_ruleid(ruleid: str) -> bool:
    return all(Cat.query(category) for category in ruleid.split("_"))


RuleID.learn_witness_condition(valid_ruleid)


Id = BType("Id")


def lex(id_: str, cat: str) -> RecType:
    return RecType(
        {
            "cat": SingletonType(Cat, cat),
            "id": SingletonType(Id, id_),
        }
    )
