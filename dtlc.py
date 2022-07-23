import re
from typing import *
from fphack import pipefy, pipefy_builtins, ExceptionMonad, adt, map, reduce, filter

# Hacky setup
pipefy_builtins(__name__)

Term, App, Var, Lamb = adt("Term", 
                           "App f arg",
                           "Var name",
                           "Lamb var body")

def freevars(t):
    assert isinstance(t, Term)
    if type(t) is App:
        return freevars(t.f) | freevars(t.arg)
    elif type(t) is Var:
        return {t.name}
    elif type(t) is Lamb:
        return freevars(t.body) - {t.var}
    else:
        assert False, f"invalid value {t}"

def test_freevars():
    assert freevars(App(Var("x"), Var("y"))) == {"x", "y"}
    assert freevars(Var("x")) == {"x"}
    assert freevars(Lamb("x", Var("x"))) == set()
    assert freevars(Lamb("x", App(Var("y"), Var("x")))) == {"y"}

def whnf(t):
    def spine(t, args=[]):
        if type(t) is App:
            return spine(t.f, [a, *args])
        elif type(t) is Lamb:
            assert len(args) > 1
            a, *args = args
            return spine(subst(t1.var, a, t1.body), args)
        else:
            return reduce(App, f, args)
    return spine(t)

@pipefy
def subst(var, replacement, term):
    assert type(var) is str
    assert isinstance(replacement, Term)
    assert isinstance(term, Term)
    if type(term) is Var:
        if term.name == var:
            return replacement
        else:
            return term
    elif type(term) is App:
        return App(subst(var, replacement, term.f), 
                   subst(var,replacement, term.arg))
    elif type(term) is Lamb:
        if term.var == var:
            return term
        elif term.var in freevars(replacement):
            new_termvar = freshvar(term.var, freevars(term.body) | freevars(replacement))
            new_body = subst(term.var, Var(new_termvar), term.body) @ subst(var, replacement, ...)
            return Lamb(new_termvar, new_body)
        else:
            return Lamb(term.var, subst(var, replacement, term.body))
    else:
        assert False

def test_subst():
    assert subst("x", Var("replacement"), Var("x")) == Var("replacement")
    assert subst("x", Var("replacement"), Lamb("x", Var("x"))) == Lamb("x", Var("x"))
    assert subst("x", Var("replacement"), Lamb("y", Var("x"))) == Lamb("y", Var("replacement"))
    assert subst("x", Var("replacement"), Lamb("replacement", Var("x"))) == Lamb("replacement0", Var("replacement"))
    assert subst("x", Var("replacement"), App(Var("x"), Var("x"))) == App(Var("replacement"), Var("replacement"))

def freshvar(var, freevarset, i = 0):
    assert type(var) is str
    assert type(freevarset) is set
    if var in freevarset:
        if i > 0:
            var = re.search(r"[a-zA-Z]+", var).group(0)
            return freshvar(f"{var}{i}", freevarset, i + 1)
        else:
            return freshvar(f"{var}{i}", freevarset, i + 1)
    else:
        return var

def test_freshvar():
    assert freshvar("x", set()) == "x"
    assert freshvar("x", {"x"}) == "x0"
    assert freshvar("x", {"x", "x0"}) == "x1"
    s = {"x"} | {f"x{i}" for i in range(0, 100)}
    assert freshvar("x", s) == "x100"

def alpha_eq(term1, term2):
    assert isinstance(term1, Term)
    assert isinstance(term1, Term)
    if type(term1) is not type(term2):
        return False
    elif type(term1) is Var:
        return term1 == term2
    elif type(term1) is App:
        return alpha_eq(term1.f, term2.f) and alpha_eq(term1.arg, term2.arg)
    elif type(term1) is Lamb:
        return alpha_eq(term1.body, subst(term2.var, Var(term1.var), term2.body))
    else:
        assert False

def test_alpha_eq():
    assert alpha_eq(Var("x"), Var("x"))
    assert not alpha_eq(Var("x"), Var("y"))
    assert alpha_eq(Lamb("x", Var("x")), Lamb("y", Var("y")))
    assert not alpha_eq(Lamb("x", Var("y")), Lamb("y", Var("y")))
    assert alpha_eq(App(Lamb("x", Var("x")), Var("z")), App(Lamb("y", Var("y")), Var("z")))

def normal_form(term):
    assert isinstance(term, Term)
    def spine(term, args):
        if type(term) is App:
            return spine(term.f, [term.arg, *args])
        elif type(term) is Lamb:
            if not args:
                return Lamb(term.var, normal_form(term.body))
            else:
                arg, *args = args
                return spine(subst(term.var, arg, term.body), args)

        else:
            return reduce(App, map(normal_form, args), term)
    return spine(term, [])

def beta_eq(term1, term2):
    assert isinstance(term1, Term)
    assert isinstance(term2, Term)
    return alpha_eq(normal_form(term1), normal_form(term2))


def lamb(*args):
    "construct mutli arguments lambdas"
    *args, body = args
    body = Var(body) if type(body) is str else body
    return reduce(lambda acc, arg: Lamb(arg, acc), reversed(args), body)

def app(*args):
    "construct multi arguments applications"
    f, *args = (Var(arg) if type(arg) is str else arg for arg in args)
    return reduce(lambda acc, arg: App(acc, arg), args, f)


def test_beta_eq():
    assert lamb("a", "a") == Lamb("a", Var("a"))
    assert lamb("a", "b", "a") == Lamb("a", Lamb("b", Var("a")))
    assert app("a", "b") == App(Var("a"), Var("b"))
    assert app("a", "b", "c") == App(App(Var("a"), Var("b")), Var("c"))

    assert beta_eq(app(lamb("a", "a"), "b"), Var("b"))
    assert beta_eq(app(lamb("a", "b"), "c"), Var("b"))

    true = lamb("a", "b", "a")
    false = lamb("a", "b", "b")

    assert beta_eq(app(true, "x", "y"), Var("x"))
    assert beta_eq(app(false, "x", "y"), Var("y"))

    assert beta_eq(app(lamb("x", "y", app("x", "y")), "y"),
                   lamb("y0", app("y", "y0")))

    zero = lamb("s", "z", "z")
    one = lamb("s", "z", app("s", "z"))
    two = lamb("s", "z", app("s", app("s", "z")))
    tree = lamb("s", "z", app("s", app("s", app("s", "z"))))
    plus = lamb("m", "n", "s", "z", app("m", "s", app("n", "s", "z")))

    assert normal_form(app(plus, zero, zero)) == zero
    assert normal_form(app(plus, zero, one)) == one
    assert normal_form(app(plus, one, zero)) == one
    assert normal_form(app(plus, one, one)) == two
    assert normal_form(app(plus, one, two)) == tree
    six = app(plus, tree, tree)
    four = app(plus, two, two)
    assert beta_eq(app(plus, four, two), six)


