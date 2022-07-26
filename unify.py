from typing import *
from dataclasses import dataclass
from collections import namedtuple
from functools import partial, reduce

from fphack import *

def show_term(t):
    if type(t) is Var:
        return t.name
    elif type(t) is Func:
        if not t.args:
            return t.name
        elif t.name == "arrow":
            return " -> ".join(map(show_term, t.args))
        else:
            args = ", ".join(t.args)
            return f"{t.name}({args})"

Term, Var, Func = Data("Term") \
    | "Var name" \
    > "Func name args"
Term.__repr__ = show_term

def const(name):
    return Func(name, tuple())

def safe_const(name):
    if type(name) is str:
        if name.isupper():
            return Var(name)
        else:
            return const(name)
    else:
        return name

def func(name, *args):
    return Func(name, tuple(safe_const(arg) for arg in args))

def arrow(*args):
    assert len(args) >= 2
    return func("arrow", *args)

def subst(subs, t):
    if type(t) is Var:
        for (sname, sterm) in subs:
            if sname == t.name:
                return sterm
        else:
            return t
    elif type(t) is Func:
        return Func(t.name, tuple(subst(subs, arg) for arg in t.args))
    else:
        raise ValueError

def multsubst(subs1, subs2):
    return {(x, subst(subs2, t)) for (x, t) in subs1}

def occurs_check(needle, haystack):
    assert isinstance(needle, Term)
    assert isinstance(haystack, Term)

    if type(haystack) is Var:
        return False
    elif type(haystack) is Func:
        return any(ocurrs_check(needle, arg) for arg in haystack.args)
    else:
        assert False, "Oops {needle} {haystack}"

def unify(t1, t2, u = set()):
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
        if occurs_check(t1, t2):
            raise ValueError(f"Unification error, {t1} ocurrs in {t2}")
        newu = {(t1.name, t2)}
        return multsubst(newu, u)
    else:
        raise ValueError(f"Unification error, unexpected error, {t1} {t2}")

def test_subst():
    assert subst({("X", Var("Y"))}, Var("X")) == Var("Y")
    assert subst({}, Var("X")) == Var("X")
    assert subst({("X", Var("Y")), ("Y", Var("X"))}, func("f", "X", "Y")) == func("f", "Y", "X")
    assert subst({("X", Var("Y")), ("Y", Var("X"))}, func("f", "Y", "X")) == func("f", "X", "Y")

def test_unify():
    assert unify(Var("X"), const("a")) == {("X", const("a"))}
    assert unify(func("f", "X"), func("f", "a")) == {("X", const("a"))}
    assert unify(func("f", "X"), func("f", "Y")) == {("X", Var("Y"))}
    assert unify(func("f", "X", "b"), func("f", "a", "Y")) == {("X", const("a")), ("Y", const("b"))}

    assert unify(arrow(func("list", "A"), func("option", "A")),
                 arrow(func("list", "int"), func("option", "int"))) == {("A", const("int"))}
