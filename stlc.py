import re
from typing import *
from fphack import pipefy, pipefy_builtins, ExceptionMonad, Data, map, reduce, filter, list as list_
from miniparser import pregex, pand, por # type: ignore

# Hacky setup
pipefy_builtins(__name__)

Term, App, Var, Lamb, Arrow, Int, Bool = Data("Term") \
    | "App f arg" \
    | "Var name"  \
    | "Lamb var typ body"  \
    | "Arrow arg ret" \
    | "Int" \
    > "Bool"

class TypeEnv:
    def __init__(self, **data):
        self._data = data
    def extend(self, d):
        return TypeEnv(**{**self._data, **d})
    def __add__(self, d):
        return self.extend(d)
    def __getitem__(self, k):
        return self._data[k]

@pipefy
def typecheck(term, env=TypeEnv()):
    assert type(env) is TypeEnv
    assert isinstance(term, Term)
    if type(term) is Var:
        return env[term.name]
    elif type(term) is App:
        tf = typecheck(term.f, env)
        if type(tf) is not Arrow:
            raise TypeError(f"Expected a function type found a {tf}")
        ta = typecheck(term.arg, env)
        if ta != tf.arg:
            raise TypeError(f"Expected a {tf.arg}, found a {ta}")
        return tf.ret
    elif type(term) is Lamb:
        newenv = env + {term.var: term.typ}
        tbody = typecheck(term.body, newenv)
        return Arrow(term.typ, tbody)
    else:
        assert False

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
    assert freevars(Lamb("x", Int(), Var("x"))) == set()
    assert freevars(Lamb("x", Int(), App(Var("y"), Var("x")))) == {"y"}

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
            return Lamb(new_termvar, term.typ, new_body)
        else:
            return Lamb(term.var, term.typ, subst(var, replacement, term.body))
    else:
        assert False

def test_subst():
    assert subst("x", Var("replacement"), Var("x")) == Var("replacement")
    assert subst("x", Var("replacement"), Lamb("x", Int(), Var("x"))) == Lamb("x", Int(), Var("x"))
    assert subst("x", Var("replacement"), Lamb("y", Int(), Var("x"))) == Lamb("y", Int(), Var("replacement"))
    assert subst("x", Var("replacement"), Lamb("replacement", Int(), Var("x"))) == Lamb("replacement0", Int(), Var("replacement"))
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
        return term1.typ == term2.typ and alpha_eq(term1.body, subst(term2.var, Var(term1.var), term2.body))
    else:
        assert False

def test_alpha_eq():
    assert alpha_eq(Var("x"), Var("x"))
    assert not alpha_eq(Var("x"), Var("y"))
    assert alpha_eq(Lamb("x", Int(), Var("x")), Lamb("y", Int(), Var("y")))
    assert not alpha_eq(Lamb("x", Int(), Var("y")), Lamb("y", Int(), Var("y")))
    assert alpha_eq(App(Lamb("x", Int(), Var("x")), Var("z")), App(Lamb("y", Int(), Var("y")), Var("z")))
    assert not alpha_eq(Lamb("x", Int(), Var("x")), Lamb("y", Bool(), Var("y")))

def normal_form(term):
    assert isinstance(term, Term)
    def spine(term, args):
        if type(term) is App:
            return spine(term.f, [term.arg, *args])
        elif type(term) is Lamb:
            if not args:
                return Lamb(term.var, term.typ, normal_form(term.body))
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


def tokenize_type(s):
    return s.split("(") @ map(lambda x : x.split(")"), ...) @ list_(...)
    
LPAR = pregex(r"\(")
RPAR = pregex(r"\)")
ARROW = pregex(r"->")
VAR = pregex(r"\w+")

def pvar(inp):
    v, inp = VAR(inp)
    if v == "int":
        return Int(), inp
    elif v == "bool":
        return Bool(), inp
    else:
        assert False, "unexpected type {inp}"
def parrow(inp):
    (t1, _, t2), inp = pand(patom, ARROW, pexpr)(inp)
    return Arrow(t1, t2), inp
def ppar(inp):
    (_, e, _), inp = pand(LPAR, pexpr, RPAR)(inp)
    return e, inp
def patom(inp):
    return por(ppar, pvar)(inp)
def pexpr(inp):
    return por(parrow, patom)(inp)
def typ(inp):
    return pexpr(inp)[0]

def test_typ_parser():
    assert typ("bool") == Bool()
    assert typ("int") == Int()
    assert typ("int -> bool") == Arrow(Int(), Bool())
    assert typ("int -> int -> bool") == Arrow(Int(), Arrow(Int(), Bool()))
    assert typ("(int -> int) -> bool") == Arrow(Arrow(Int(), Int()), Bool())

def lamb(*args):
    "construct mutli arguments lambdas"
    *args, body = args
    body = Var(body) if type(body) is str else body
    def fold_f(body, arg):
        assert ":" in arg, f"syntax error, missing the type annotaion (\": some_type\") in {arg}"
        arg, typ_ = arg.split(":", 1) @ map(str.strip, ...) @ list_(...)
        return Lamb(arg, typ(typ_), body) 
    return reduce(fold_f, reversed(args), body)

def app(*args):
    "construct multi arguments applications"
    f, *args = (Var(arg) if type(arg) is str else arg for arg in args)
    return reduce(lambda acc, arg: App(acc, arg), args, f)

def test_typecheck():
    def typchk(t, env=None):
        env = TypeEnv() if env is None else env
        return ExceptionMonad.ret(t) @ typecheck(..., env)

    assert typchk(Var("x"), TypeEnv(x=Int())) == typ("int")
    assert typchk(lamb("x : int", "x")) == typ("int -> int")
    assert typchk(app(lamb("b : bool", "b"), "i"), TypeEnv(i=typ("int"))) == TypeError("Expected a Bool(), found a Int()")

    id_int = lamb("x : int", "x")
    apply_f = lamb("f : int -> int", "x : int", app("f", "x"))
    assert typchk(app(apply_f, id_int, "i"), TypeEnv(i=Int())) == typ("int")

def test_beta_eq():
    assert lamb("a : int", "a") == Lamb("a", Int(), Var("a"))
    assert lamb("a : int", "b : bool", "a") == Lamb("a", Int(), Lamb("b", Bool(), Var("a")))
    assert app("a", "b") == App(Var("a"), Var("b"))
    assert app("a", "b", "c") == App(App(Var("a"), Var("b")), Var("c"))

    assert beta_eq(app(lamb("a : int", "a"), "b"), Var("b"))
    assert beta_eq(app(lamb("a : int", "b"), "c"), Var("b"))

    true = lamb("a : bool", "b : bool", "a")
    false = lamb("a : bool", "b : bool", "b")

    assert beta_eq(app(true, "x", "y"), Var("x"))
    assert beta_eq(app(false, "x", "y"), Var("y"))

    assert beta_eq(app(lamb("x : int", "y : bool", app("x", "y")), "y"),
                   lamb("y0 : bool", app("y", "y0")))

    id_int = lamb("x : int", "x")
    apply_f = lamb("f : int -> int", "x : int", app("f", "x"))
    assert beta_eq(app(apply_f, id_int, "i"), Var("i"))

    # @TODO type annotate these functions
    # zero = lamb("s", "z", "z")
    # one = lamb("s", "z", app("s", "z"))
    # two = lamb("s", "z", app("s", app("s", "z")))
    # tree = lamb("s", "z", app("s", app("s", app("s", "z"))))
    # plus = lamb("m", "n", "s", "z", app("m", "s", app("n", "s", "z")))

    # assert normal_form(app(plus, zero, zero)) == zero
    # assert normal_form(app(plus, zero, one)) == one
    # assert normal_form(app(plus, one, zero)) == one
    # assert normal_form(app(plus, one, one)) == two
    # assert normal_form(app(plus, one, two)) == tree
    # six = app(plus, tree, tree)
    # four = app(plus, two, two)
    # assert beta_eq(app(plus, four, two), six)


