import re
from typing import *
from fphack import pipefy, pipefy_builtins, ExceptionMonad, Data, map, reduce, filter, list as list_, reversed, partial

# Hacky setup
pipefy_builtins(__name__)



Kinds, Star, Box = Data("Kinds") | "Star" > "Box"
Term, App, Var, Lamb, Forall, Kind = Data("Term") \
    | "App f arg" \
    | "Var name"  \
    | "Lamb var typ body"  \
    | "Forall var typ body" \
    > "Kind kind"


class TypeEnv:
    def __init__(self, **data):
        self._data = data
    def extend(self, d):
        return TypeEnv(**{**self._data, **d})
    def __add__(self, d):
        return self.extend(d)
    def __getitem__(self, k):
        if k not in self._data:
            raise KeyError(f"Unbound variable {k} not in scope {self._data}")
        return self._data[k]

allowed_kinds = {
    (Kind(Star()), Kind(Star())),
    (Kind(Star()), Kind(Box())),
    (Kind(Box()), Kind(Star())),
    (Kind(Box()), Kind(Box())),
}

initial_typeenv = TypeEnv(**{
    "int": Kind(Star()),
    "bool": Kind(Star()),
})
# the base types
Int = lambda: Var("int")
Bool = lambda: Var("bool")


def trace_typecheck(tc):
    def wrapper(term, env=initial_typeenv):
        print(f"> typechecking {env._data} |- {term}")
        t = tc(term, env)
        print(f"< typechecking {env._data} |- {term} : {t}")
        return t
    return wrapper


@pipefy
@trace_typecheck
def typecheck(term, env=initial_typeenv):
    assert type(env) is TypeEnv
    assert isinstance(term, Term)
    if type(term) is Var:
        return env[term.name]
    elif type(term) is App:
        app = term
        tf = typecheck(app.f, env)
        if type(tf) is Forall:
            ta = typecheck(app.arg, env)
            if not beta_eq(ta, tf.typ):
                raise TypeError(f"Expected a {tf.typ}, found a {ta}")
            return subst(tf.var, app.arg, tf.body)
    elif type(term) is Lamb:
        typecheck(term.typ, env)
        newenv = env + {term.var: term.typ}
        tbody = typecheck(term.body, newenv)
        lt = Forall(term.var, term.typ, tbody)
        typecheck(lt, env)
        return lt
    elif type(term) is Forall:
        s = typecheck_red(term.typ, env)
        newenv = env + {term.var: term.typ}
        t = typecheck_red(term.body, newenv)
        if (s, t) not in allowed_kinds:
            raise TypeError("Bad abstraction")
        return t
    elif type(term) is Kind:
        if type(term.kind) is Star:
            return Kind(Box())
        elif type(term.kind) is Box:
            raise TypeError("Invalid kind Box at term")
        else:
            assert False
    else:
        assert False

def typecheck_red(term, env):
    return typecheck(term, env) @ whnf(...)

def freevars(t):
    assert isinstance(t, Term)
    if type(t) is App:
        return freevars(t.f) | freevars(t.arg)
    elif type(t) is Var:
        return {t.name}
    elif type(t) is Kind:
        return {}
    elif type(t) is Lamb or type(t) is Forall:
        return freevars(t.body) - {t.var}
    else:
        assert False, f"invalid value {t}"

def test_freevars():
    assert freevars(App(Var("x"), Var("y"))) == {"x", "y"}
    assert freevars(Var("x")) == {"x"}
    assert freevars(Lamb("x", Int(), Var("x"))) == set()
    assert freevars(Lamb("x", Int(), App(Var("y"), Var("x")))) == {"y"}

@pipefy
def whnf(t):
    def spine(t, args=[]):
        if type(t) is App:
            return spine(t.f, [a, *args])
        elif type(t) is Lamb or type(t) is Forall:
            assert len(args) > 1
            a, *args = args
            return spine(subst(t1.var, a, t1.body), args)
        else:
            return reduce(App, args, t)
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
    elif type(term) is Kind:
        return term
    elif type(term) is App:
        return App(subst(var, replacement, term.f), 
                   subst(var,replacement, term.arg))
    elif type(term) is Lamb or type(term) is Forall:
        if term.var == var:
            return term
        elif term.var in freevars(replacement):
            new_termvar = freshvar(term.var, freevars(term.body) | freevars(replacement))
            new_body = subst(term.var, Var(new_termvar), term.body) @ subst(var, replacement, ...)
            return type(term)(new_termvar, term.typ, new_body)
        else:
            return type(term)(term.var, term.typ, subst(var, replacement, term.body))
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
    elif type(term1) is Lamb or type(term1) is Forall:
        return beta_eq(term1.typ, term2.typ) and alpha_eq(term1.body, subst(term2.var, Var(term1.var), term2.body))
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
                return Lamb(term.var, normal_form(term.typ), normal_form(term.body))
            else:
                arg, *args = args
                return spine(subst(term.var, arg, term.body), args)
        elif type(term) is Forall:
            return reduce (App, map(normal_form, args), 
                           Forall(term.var, normal_form(term.typ), normal_form(term.body)))
        else:
            return reduce(App, map(normal_form, args), term)
    return spine(term, [])

def beta_eq(term1, term2):
    assert isinstance(term1, Term)
    assert isinstance(term2, Term)
    return alpha_eq(normal_form(term1), normal_form(term2))

def abstr(f, *args):
    assert len(args) >= 2
    *args, body = args
    args = zip(args[0::2], args[1::2]) @ list_(...) @ reversed(...) @ list_(...)
    body = Var(body) if type(body) is str else body
    def fold_f(body, arg):
        assert len(arg) is 2
        arg, typ = arg
        return f(arg, typ, body)
    return reduce(fold_f, args, body)

lamb = partial(abstr, Lamb)
forall = partial(abstr, Forall)

def app(*args):
    "construct multi arguments applications"
    f, *args = (Var(arg) if type(arg) is str else arg for arg in args)
    return reduce(lambda acc, arg: App(acc, arg), args, f)

def test_constructors():
    assert app("x", "y") == App(Var("x"), Var("y"))
    assert lamb("x", Int(), 
                "y", Int(), 
                "x") == Lamb("x", Int(), Lamb("y", Int(), Var("x")))
    assert forall("x", Int(), 
                "y", Int(), 
                "x") == Forall("x", Int(), Forall("y", Int(), Var("x")))

def test_typecheck():
    def typchk(t, env=initial_typeenv):
        return ExceptionMonad.ret(t) @ typecheck(..., env)

    assert typchk(Var("x"), TypeEnv(x=Int())) == Int()
    assert typchk(lamb("x", Int(), "x")) == Forall("x", Int(), Int())
    assert typchk(app(lamb("b", Bool(), "b"), "i"), initial_typeenv + {'i': Int()}) == TypeError("Expected a Var(name='bool'), found a Var(name='int')")

    id_int = lamb("x", Int(), "x")
    apply_f = lamb("f", forall("_", Int(), Int()), 
                   "x", Int(), 
                   app("f", "x"))
    assert typchk(app(apply_f, id_int, "i"), initial_typeenv + {"i": Int()}) == Int()

def test_beta_eq():
    assert beta_eq(app(lamb("a", Int(), "a"), "b"), Var("b"))
    assert beta_eq(app(lamb("a", Int(), "b"), "c"), Var("b"))

    nf = normal_form
    true = lamb("a", Bool(), "b", Bool(), "a")
    false = lamb("a", Bool(), "b", Bool(), "b")

    assert nf(app(true, "x", "y")) == Var("x") 
    assert nf(app(false, "x", "y")) == Var("y")

    assert beta_eq(app(lamb("x", Int(), "y", Bool(), app("x", "y")), "y"),
                   lamb("y0", Bool(), app("y", "y0")))

    id_int = lamb("x", Int(), "x")
    apply_f = lamb("f", forall("_", Int(), Int()), 
                   "x", Int(), 
                   app("f", "x"))
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


