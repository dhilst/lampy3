from typing import *
import ast
from dataclasses import dataclass

class TypeTerm:
    @staticmethod
    def from_str(input: str):
        if type(input) is not str:
            breakpoint()
        if "->" in input:
            return Arrow.from_str(input)
        elif input[0].isupper():
            return Var(input)
        else:
            return Const(input)

    @staticmethod
    def parse(input):
        name, term = (TypeTerm.from_str(x.strip()) for x in input.split(":"))
        return name, term

@dataclass(frozen=True)
class Var(TypeTerm):
    name: str

@dataclass(frozen=True)
class Arrow(TypeTerm):
    args: list[TypeTerm]

    @staticmethod
    def from_str(input):
        return Arrow([x.strip() for x in input.split("->")])

    @property
    def args_without_return(self):
        return Arrow(self.args[:-1])

@dataclass(frozen=True)
class Const(TypeTerm):
    name: str

Subst = Set[Tuple[str, TypeTerm]]

T = TypeVar("T")
class Result(Generic[T]):
    @overload
    def __init__(self, err: str): ...
    @overload
    def __init__(self, ok: T): ...

    def __init__(self, *, ok=None, err=None):
        if ok is not None:
            self.value = ok
            self.is_ok = True
        else:
            self.err = err
            self.is_ok = False

    @property
    def is_err(self):
        return not self.is_ok

class Unify:
    @staticmethod
    def subst1(term: TypeTerm, subst: Subst) -> TypeTerm:
        if type(term) is Var:
            for name, replacement in subst:
                if name == term.name:
                    return replacement
            else:
                return term
        elif type(term) is Arrow:
            return Arrow([Unify.subst1(arg, subst) for arg in term.args])
        elif type(term) is Const:
            return term
        else:
            assert False, "invalid case in subst1"

    @staticmethod
    def substmult(subst: Subst, replacement: Subst) -> Subst:
        return {(name, Unify.subst1(term, replacement)) for (name, term) in subst}

    @staticmethod
    def unify(t1: TypeTerm, t2: TypeTerm, subst: Subst = set()) -> Result[Subst]:
        if t1 == t2:
            return Result(ok=subst)
        elif type(t1) is Arrow and type(t2) is Arrow:
            if len(t1.args) != len(t1.args):
                return Result(err=f"unification error {t1} <> {t2}")
            else:
                for a1, a2 in zip(t1.args, t2.args):
                    r = Unify.unify(a1, a2, subst)
                    if r.is_err:
                        return r
                    else:
                        subst |= r.value
                return Result(ok=subst)
        elif type(t2) is Var and type(t1) is not Var:
            return Unify.unify(t2, t1, subst)
        elif type(t1) is Var:
            newsubst = {(t1.name, t2)}
            subst = Unify.substmult(subst, newsubst) | newsubst
            return Result(ok=subst)
        elif type(t1) is Const and type(t2) is Const:
            if t1.name != t2.name:
                return Result(err=f"Type error, expected {t1.name}, found {t2.name}")
            else: 
                return Result(ok=subst)
        else:
            assert False, "invalid case"

class Typechecker(ast.NodeVisitor):
    def __init__(self):
        super().__init__()
        self.typeenv = {}

    def visit_FunctionDef(self, node):
        # gatther the signature into of the
        # function from @sig decorator
        for dec in node.decorator_list:
            if dec.func.id == "sig":
                typ = Arrow([TypeTerm.from_str(x.strip()) for x 
                             in dec.args[0].value.split(":")[1].split(" -> ")])
                self.typeenv[node.name] = typ

        if not node.name in self.typeenv:
            self.generic_visit(node)
            return

        oldenv = self.typeenv.copy() # save the old environment
        self.typeenv.update({ # extend the env with the arguments
            arg.arg: typ for arg, typ 
            in zip(node.args.args, self.typeenv[node.name].args[:-1])})
        # visit children
        self.generic_visit(node)
        # restore the environment
        self.typeenv = oldenv

    def visit_Call(self, node):
        if type(node.func) is ast.Name:
            if node.func.id == "sig":
                name, typ = TypeTerm.parse(node.args[0].value)
                self.typeenv[name] = typ
                self.generic_visit(node)
                return

            elif node.func.id in self.typeenv:
                # get the arguments types
                actual_args = []
                for arg in node.args:
                    if type(arg) is ast.Constant:
                        actual_args.append(
                            TypeTerm.from_str(type(arg.value).__name__))
                    elif type(arg) is ast.Name:
                        if arg.id in self.typeenv:
                            actual_args.append(
                                self.typeenv[arg.id])
                        else:
                            # no type information,
                            # give up
                            self.generic_visit(node)
                            return
                if not actual_args:
                    self.generic_visit(node)
                    return 

                actual_args = Arrow(
                    [arg for arg in actual_args])
                expected_args = self.typeenv[node.func.id].args_without_return
                result = Unify.unify(expected_args, actual_args)
                if result.is_err:
                    raise TypeError(result.err)
                
        self.generic_visit(node)

def typecheck(text, typeenv={}):
    tree = ast.parse(text)
    Typechecker().visit(tree)


typecheck(
"""
def sig(*args, **kwargs):
    return lambda f: f

@sig("inc : float -> A -> A")
def inc(a, b):
    return a + 1

@sig("foo : int -> float")
def foo(a):
    return float(inc(a, "a"))
"""	
)
print("ok")