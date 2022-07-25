import sys
import ast
from typing import *
from dataclasses import dataclass
from fphack import map, Data

def type_(s):
    pass

def type_dump(s, t):
    pass

def arrow_from_str(input):
    return Arrow([type_from_str(x.strip()) for x in input.split("->")])

def type_from_str(input: str):
    if "->" in input:
        return arrow_from_str(input)
    elif input.startswith("!"):
        return TypeGuard(input[1:]) # type: ignore
    elif input[0].isupper():
        return Var(input)
    else:
        return Const(input)

def type_parse(input):
    name, term = input.split(":", 1) @ map(str.strip, ...)
    return name, type_from_str(term)

TypeTerm, TypeGuard, Var, Arrow, Const = Data("TypeTerm") \
    | "TypeGuard typ" \
    | "Var typ" \
    | "Arrow args" \
    > "Const name"

Result, Ok, Err = Data("Result") \
    | "Ok value" \
    > "Err err"

T = TypeVar("T")

class Unify:
    @staticmethod
    def subst1(term, subst):
        assert isinstance(term, TypeTerm)
        assert isinstance(tern, set)
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
    def substmult(subst, replacement):
        isinstance(subst, set)
        isinstance(replacement, set)
        return {(name, Unify.subst1(term, replacement)) for (name, term) in subst}

    @staticmethod
    def unify(t1, t2, subst = set()):
        assert isinstance(t1, TypeTerm)
        assert isinstance(t2, TypeTerm)
        assert isinstance(subst, set)
        if t1 == t2:
            return Ok(subst)
        elif type(t1) is Arrow and type(t2) is Arrow:
            if len(t1.args) != len(t1.args):
                return Err(f"unification error {t1} <> {t2}")
            else:
                for a1, a2 in zip(t1.args, t2.args):
                    r = Unify.unify(a1, a2, subst)
                    if type(r) is Err:
                        return r
                    else:
                        subst |= r.value
                return Ok(subst)
        elif type(t2) is Var and type(t1) is not Var:
            return Unify.unify(t2, t1, subst)
        elif type(t1) is Var:
            newsubst = {(t1.name, t2)}
            subst = Unify.substmult(subst, newsubst) | newsubst
            return OK(subst)
        elif type(t1) is Const and type(t2) is Const:
            if t1.name != t2.name:
                return Err(f"Type error, expected {t1.name}, found {t2.name}")
            else: 
                return Ok(subst)
        elif type(t1) is TypeGuard and type(t2) is TypeGuard:
            if t1.typ != t2.typ:
                return Err(f"Type error, expected {t1.typ}, found {t2.typ}")
            else: 
                return Ok(subst)
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
                name, typ = type_parse(node.args[0].value)
                self.typeenv[name] = typ
                self.generic_visit(node)
                return

            elif node.func.id in self.typeenv:
                # get the arguments types
                actual_args = []
                for arg in node.args:
                    if type(arg) is ast.Constant:
                        actual_args.append(
                            type_from_str(type(arg.value).__name__))
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
                expected_args = Arrow(self.typeenv[node.func.id].args[:-1])
                result = Unify.unify(expected_args, actual_args)
                if type(result) is Err:
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
