import sys
from typing import *
import ast
from dataclasses import dataclass
from fphack import map

class TypeTerm:
    @staticmethod
    def from_str(input: str):
        if "->" in input:
            return Arrow.from_str(input)
        elif input.startswith("!"):
            return TypeGuard(input[1:])
        elif input[0].isupper():
            return Var(input)
        else:
            return Const(input)

    @staticmethod
    def parse(input):
        name, term = input.split(":", 1) @ map(str.strip, ...)
        return name, TypeTerm.from_str(term)

@dataclass(frozen=True)
class TypeGuard(TypeTerm):
    typ: str

@dataclass(frozen=True)
class Var(TypeTerm):
    name: str

@dataclass(frozen=True)
class Arrow(TypeTerm):
    args: list[TypeTerm]

    @staticmethod
    def from_str(input):
        return Arrow([TypeTerm.from_str(x.strip()) for x in input.split("->")])

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
        elif type(term) is Const or type(term) is TypeGuard:
            return term
        else:
            assert False, f"invalid case in subst1 {term}"

    @staticmethod
    def substmult(subst: Subst, replacement: Subst) -> Subst:
        return {(name, Unify.subst1(term, replacement)) for (name, term) in subst}

    @staticmethod
    def unify(t1: TypeTerm, t2: TypeTerm, subst: Subst = set()) -> Result[Subst]:
        assert isinstance(t1, TypeTerm)
        assert isinstance(t2, TypeTerm)
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
        elif type(t1) is TypeGuard and type(t2) is TypeGuard:
            if t1.typ != t2.typ:
                return Result(err=f"Type error, expected {t1.typ}, found {t2.typ}")
            else: 
                return Result(ok=subst)
        else:
            assert False, f"invalid case {t1} {t2}"

class Typechecker(ast.NodeVisitor):
    def __init__(self):
        super().__init__()
        self.typeenv = {}

    def visit_If(self, node):
        if (type(node.test) is ast.Call and type(node.test.func) is ast.Name and 
            node.test.func.id in self.typeenv and 
            type(self.typeenv[node.test.func.id].args[-1]) is TypeGuard and
            len(node.test.args) == 1
            ):
            typeguard = self.typeenv[node.test.func.id].args[-1]
            call = node.test.func
            arg = node.test.args[0].id
            oldenv = self.typeenv.copy()
            self.typeenv[arg] = Const(typeguard.typ)
            for node_ in node.body:
                self.generic_visit(node_)
            self.typeenv = oldenv
            for node_ in node.orelse:
                self.generic_visit(node_)
        else:
            self.generic_visit(node)

    def visit_Assign(self, node):
        self.generic_visit(node)

    def visit_FunctionDef(self, node):
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
            if node.func.id == "type_dump":
                msg = node.args[0].value
                name = node.args[1].id
                print(msg, f"{name} : {self.typeenv.get(name, 'NOT FOUND')}")
                self.generic_visit(node)
                return

            elif node.func.id == "type_":
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
                    print("Typecheck error: ", result.err, file=sys.stderr)
                
        self.generic_visit(node)

def typecheck(text, typeenv={}):
    tree = ast.parse(text)
    Typechecker().visit(tree)


typecheck(
"""
# type introduces a type
def type_(s): ...

# ! at the begining introduces a typeguard
# typeguards coerce its arguments inside if bodies
type_("is_positive : int -> !positive")
def is_positive(x):
    return x >= 1

# typechecked, never called with x < 1
type_("sub : positive -> int")
def sub(x):
    return x - 1

# x has type int
type_("x : int")
x = 1

if is_positive(x):
   # x has type positive here
   type_dump("inside if", x)
   sub(x)

type_dump("outside if", x)
sub(x)

type_("non_empty : list -> !non_empty")
def non_empty(l):
    return len(l) >= 1

type_("head : non_empty -> A")
def head(l):
    return l[0]

type_("l : list")
l = [1]
type_dump("created list", l)

type_("id_ : B -> B")
id_ = lambda x: x

if non_empty(l):
    # typechecked
    type_dump("inside if", l)
    id_(head(l))

head(l)
"""	
)


