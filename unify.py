from typing import *
from dataclasses import dataclass
from collections import namedtuple
from functools import partial, reduce

dataclass = dataclass(frozen=True) # type: ignore

@dataclass
class Term:
    name: str

@dataclass
class Var(Term):
    name: str

@dataclass
class Func(Term):
    name: str
    args: list[Term]
    
    def __hash__(self):
        if not self.args:
            return hash(self.name)
        return hash(self)

def const(name) -> Func:
    return Func(name, [])

Subs = Set[Tuple[str, Term]]

def subst(subs: Subs, t: Term) -> Term:
    if type(t) is Var:
        for (sname, sterm) in subs:
            if sname == t.name:
                return sterm
        else:
            return t
    elif type(t) is Func:
        return Func(t.name, [subst(subs, arg) for arg in t.args])
    else:
        raise ValueError

def multsubst(subs1: Subs, subs2: Subs) -> Subs:
    return {(x, subst(subs2, t)) for (x, t) in subs1}

def unify(t1: Term, t2: Term, u: Subs = set()) -> Subs:
    if t1 == t2:
        return u
    elif type(t2) is Var and type(t1) is not Var:
        return unify(t2, t1, u)
    elif type(t1) is Func and type(t2) is Func:
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            raise ValueError(f"unification error {t1.name} != {t2.name} or {len(t1.args)} != {len(t2.args)}")
        else:
            return reduce(
                lambda u, args: u | unify(args[0], args[1], u), 
                zip(t1.args, t2.args), u)
    elif type(t1) is Var:
        newu = {(t1.name, t2)}
        return multsubst(newu, u)
    else:
        raise ValueError("Unification error, unexpected error")

def test_subst():
    assert subst({("X", Var("Y"))}, Var("X")) == Var("Y")
    assert subst({}, Var("X")) == Var("X")
    assert subst({("X", Var("Y")), ("Y", Var("X"))}, Func("f", [Var("X"), Var("Y")])) == Func("f", [Var("Y"), Var("X")])
    assert subst({("X", Var("Y")), ("Y", Var("X"))}, Func("f", [Var("Y"), Var("X")])) == Func("f", [Var("X"), Var("Y")])

def test_unify():
    assert (unify(Var("X"), const("a")) == {("X", const("a"))})
    assert (unify(Func("f", [Var("X")]), Func("f", [const("a")])) == {("X", const("a"))})
    assert (unify(Func("f", [Var("X")]), Func("f", [Var("Y")])) == {("X", Var("Y"))})
    assert (unify(Func("f", [Var("X"), const("b")]), Func("f", [const("a"), Var("Y")])) == {("X", const("a")), ("Y", const("b"))})
