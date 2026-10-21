
from pyttr.categorical import SingletonType, RecType, BType, Fun, Rec, ListType, AbsPath, Re


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

def rule_binary(id_: str, mother: str, daughter1: str, daughter2: str) -> Fun :
    return Fun (
        "r1",
        RecType({"cat":SingletonType(Cat, daughter1), "id":Id}),
        Fun (
            "r2",
            RecType({"cat":SingletonType(Cat, daughter2), id:Id}),
            RecType({
                "cat":SingletonType(Cat, mother),
                "id":(
                    Fun (
                        "v1",
                        Id,
                        Fun ("v2", Id, SingletonType(Id, [id_,"r1","r2"]))),
                    [AbsPath("r1", "id"), AbsPath("r2", "id")]),
                "daughters":RecType({
                    "first":SingletonType(RecType({"cat":SingletonType(Cat, daughter1)}), "r1"),
                    "rest":RecType({
                        "first":SingletonType(RecType({"cat":SingletonType(Cat, daughter2)}), "r2"),
                        "rest":SingletonType(ListType(Re), [])}
                        )
                    }
                    )
                }
        )))
