import re
from typing import *
from dataclasses import dataclass
from lark import Lark, Transformer as LarkTransformer, Token
from io import StringIO as S
import os

grammar = r"""
    start : expr_0
    ?expr_0 : fun | from_import | expr_1
    ?expr_1 : let | ifelse | var | const


    fun             : "fun"i CNAME (CNAME+) "=" expr_0
    from_import     : "from"i (CNAME | qname) "import"i CNAME+ "end"i

    let             : "let"i CNAME "=" expr_0 "in" expr_0
    ifelse          : "if"i expr_1 "then"i expr_1 "else"i expr_1

    ?const : bool
    qname : CNAME ("." CNAME)*
    var : CNAME
    bool : BOOL 

    BOOL.10 : "true"i | "false"i

    %import common.WS
    %import common.ESCAPED_STRING
    %import common.CNAME
    %import common.SH_COMMENT
    %import common.INT
    %import common.NUMBER
    %ignore WS
    %ignore SH_COMMENT
"""

let_parser = Lark(grammar, parser="lalr")


def parse(input_):
    return Transmformator().transform(let_parser.parse(input_))


class AST:
    pass


@dataclass
class TList(AST):
    values: List[AST]


@dataclass
class TBool(AST):
    value: bool


@dataclass
class TLet(AST):
    var: str
    e1: AST
    e2: AST


@dataclass
class TVar(AST):
    name: str


@dataclass
class TFromImport(AST):
    module: str
    symbols: List[str]


@dataclass
class TFun(AST):
    name: str
    args: List[str]
    body: AST


@dataclass
class TIfElse(AST):
    cond: AST
    then: AST
    else_: AST


class Transmformator(LarkTransformer):
    def __init__(self):
        self.statements = []

    def start(self, tree):
        return tree[0]

    def bool(self, tree):
        v = tree[0].value
        if v == "true":
            return TBool(True)
        elif v == "false":
            return TBool(False)

        raise ValueError

    def var(self, tree):
        return TVar(tree[0].value)

    def let(self, tree):
        v, e1, e2 = tree
        return TLet(v, e1, e2)

    def from_import(self, tree):
        return TFromImport(tree[0], [t.value for t in tree[1:]])

    def fun(self, tree):
        name, *args, body = tree
        return TFun(name, args, body)

    def ifelse(self, tree):
        return TIfElse(*tree)


def test_parse():
    assert parse("true") == TBool(True)
    assert parse("false") == TBool(False)
    assert parse("let x = true in x") == TLet("x", TBool(True), TVar("x"))
    assert parse("from foo import bar tar zar end") == TFromImport(
        "foo", "bar tar zar".split()
    )

    assert parse("fun id x = x") == TFun("id", ["x"], TVar("x"))
    assert parse("fun const a b = a") == TFun("const", ["a", "b"], TVar("a"))

    assert parse("if true then false else true") == TIfElse(
        TBool(True), TBool(False), TBool(True)
    )


# Compiling stuff
def indent(i):
    return " " * i * 4


def compile(ast, i=0):
    if type(ast) is TBool:
        return "True" if ast.value else "False"
    elif type(ast) is TLet:
        s = S()
        s.write(f"{indent(i)}{ast.var} = {compile(ast.e1, 0)}\n")
        s.write(f"{indent(i)}{compile(ast.e2, 0)}\n")
        return s.getvalue()
    elif type(ast) is TVar:
        return f"{indent(i)}{ast.name}"
    elif type(ast) is TFromImport:
        return f"from {ast.module} import {','.join(ast.symbols)}\n"
    elif type(ast) is TFun:
        s = S()
        s.write(indent(i))
        s.write(f"def {ast.name}")
        s.write("(")
        s.write(", ".join(ast.args))
        s.write("):\n")
        s.write(indent(i))
        body = compile(ast.body, i + 1)
        body = [b for b in body.split("\n") if b]
        body[-1] = re.sub(r"(\s+)(.*)", r"\1return \2\n", body[-1])
        body = "\n".join(body)
        s.write(body)
        return s.getvalue()
    elif type(ast) is TIfElse:
        return f"{indent(i)}{compile(ast.then)} if {compile(ast.cond)} else {compile(ast.else_)}"


def pcompile(inp):
    return compile(parse(inp))


def test_compile():
    assert pcompile("true") == "True"
    assert (
        pcompile("let x = true in x")
        == """\
x = True
x
"""
    )

    assert (
        pcompile("from foo import bar tar zar end") == "from foo import bar,tar,zar\n"
    )

    assert (
        pcompile("fun id x = x")
        == """\
def id(x):
    return x
"""
    )

    assert (
        pcompile("fun foo x = let y = true in y")
        == """\
def foo(x):
    y = True
    return y
"""
    )

    assert pcompile("if true then false else true") == "False if True else True"

    assert (
        pcompile("let x = true in let y = false in z")
        == """\
x = True
y = False
z

"""
    )
