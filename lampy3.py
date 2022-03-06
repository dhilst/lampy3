import sys
import re
from argparse import ArgumentParser
from tempfile import NamedTemporaryFile
from subprocess import run
from typing import *
from dataclasses import dataclass
from lark import Lark, Transformer as LarkTransformer, Token
from io import StringIO as S

grammar = r"""
    start : script
    ?script : stmt | (stmt ";")+

    ?stmt : def_ | import_ | from_import | type_ | expr_1
    ?expr_1 : let | ifelse | bin_expr | fun | expr_2
    ?expr_2 : appl
    ?expr_3 :  var | const | atom

    type_ : "type"i CNAME "="i tyexpr_1
    ?tyexpr_1 : tyatom | tyarrow
    ?tyatom : tyconst | tyvar | "(" tyexpr_1 ")"
    !tyvar : /[a-z]/
    !tyconst : "int" | "bool" | "string"
    tyarrow : tyatom ("->" tyexpr_1)+

    block : expr_1 | (expr_1 ";")+

    def_            : "def"i CNAME ((CNAME+) | unit) "=" block "end"i?
    from_import     : "from"i qname "import"i qname+
    import_          : "import"i qname

    fun             : "fun"i (CNAME+ | unit) "=>" expr_1
    let             : "let"i CNAME "=" expr_1 "in" expr_1
    ifelse          : "if"i expr_1 "then"i expr_1 "else"i expr_1
    bin_expr : expr_1 (OP expr_1)+
    ?appl : appl expr_3+ | expr_3
    ?atom : "(" expr_1 ")"

    ?const : bool | ESCAPED_STRING -> string | INT -> integer | unit
    ?unit : "()"
    qname : CNAME ("." CNAME)*
    var : qname
    bool : BOOL

    OP : "*" | "+" | "-" | "/" | ">=" | "<=" | "==" | "!=" | ">" | "<"
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

let_parser = Lark(grammar, parser="lalr", debug=True)


def parse(input_):
    return Transmformator().transform(let_parser.parse(input_))


class AST:
    pass


class TAST:
    pass


@dataclass
class TyArrow(TAST):
    t1: TAST
    t2: TAST


@dataclass
class TyConst(TAST):
    typ: str


@dataclass
class TyVar(TAST):
    var: str


@dataclass
class TyDecl(TAST):
    name: str
    typ: TAST


@dataclass
class TList(AST):
    values: List[AST]


@dataclass
class TApply(AST):
    fname: AST
    args: List[AST]


@dataclass
class TUnit(AST):
    pass


@dataclass
class TBool(AST):
    value: bool


@dataclass
class TLet(AST):
    var: str
    e1: AST
    e2: AST


@dataclass
class TString(AST):
    value: str


@dataclass
class TInteger(AST):
    value: int


@dataclass
class TVar(AST):
    name: str


@dataclass
class TFromImport(AST):
    module: str
    symbols: List[str]


@dataclass
class TImport(AST):
    module: str


@dataclass
class TBlock(AST):
    exprs: List[AST]


@dataclass
class TDef(AST):
    name: str
    args: Union[List[TUnit], List[str]]
    body: TBlock


@dataclass
class TFun(AST):
    args: Union[List[TUnit], List[str]]
    body: AST


@dataclass
class TIfElse(AST):
    cond: AST
    then: AST
    else_: AST


@dataclass
class TScript(AST):
    exprs: List[AST]


@dataclass
class TBin(AST):
    values: List[AST]


@dataclass
class TOp(AST):
    op: str


class Transmformator(LarkTransformer):
    def __init__(self):
        self.statements = []

    def type_(self, tree):
        return TyDecl(tree[0].value, tree[1])

    def tyvar(self, tree):
        return TyVar(tree[0].value)

    def tyarrow(self, tree):
        return TyArrow(tree[0], tree[1])

    def tyconst(self, tree):
        return TyConst(tree[0].value)

    def unit(self, _):
        return TUnit()

    def start(self, tree):
        return tree[0]

    def bool(self, tree):
        v = tree[0].value
        if v == "true":
            return TBool(True)
        elif v == "false":
            return TBool(False)

        raise ValueError

    def string(self, tree):
        return TString(tree[0].value[1:-1])  # remove quotes

    def integer(self, tree):
        return TInteger(int(tree[0].value))

    def var(self, tree):
        return TVar(tree[0])

    def let(self, tree):
        v, e1, e2 = tree
        return TLet(v, e1, e2)

    def import_(self, tree):
        return TImport(tree[0])

    def from_import(self, tree):
        return TFromImport(tree[0], tree[1:])

    def qname(self, tree):
        return ".".join(tree)

    def block(self, tree):
        return TBlock(tree)

    def def_(self, tree):
        name, *args, body = tree
        return TDef(name, args, body)

    def fun(self, tree):
        *args, body = tree
        return TFun(args, body)

    def ifelse(self, tree):
        return TIfElse(*tree)

    def appl(self, tree):
        fname, *args = tree
        return TApply(fname, args)

    def script(self, tree):
        return TScript(tree)

    def bin_expr(self, tree):
        values: List[AST] = []
        for t in tree:
            if type(t) is Token and t.type == "OP":
                values.append(TOp(t.value))
            elif isinstance(t, AST):
                values.append(t)
            else:
                raise TypeError(f"Unexpected type at {t}")

        return TBin(values)


def test_parse():
    assert parse("true") == TBool(True)
    assert parse("false") == TBool(False)
    assert parse("let x = true in x") == TLet("x", TBool(True), TVar("x"))
    assert parse("from foo import bar tar zar") == TFromImport(
        "foo", "bar tar zar".split()
    )

    assert parse("def id x = x end") == TDef(
        "id", ["x"], TBlock(exprs=[TVar(name="x")])
    )
    assert parse("def const a b = a end") == TDef(
        "const", ["a", "b"], TBlock(exprs=[TVar(name="a")])
    )

    assert parse("if true then false else true") == TIfElse(
        TBool(True), TBool(False), TBool(True)
    )

    assert parse("foo foo") == TApply(TVar("foo"), [TVar("foo")])
    assert parse("foo foo foo") == TApply(TVar("foo"), [TVar("foo"), TVar("foo")])

    assert parse('"foo"') == TString("foo")
    assert parse("100") == TInteger(100)
    assert parse("100 * 100") == TBin([TInteger(100), TOp("*"), TInteger(100)])

    assert parse("foo ()") == TApply(fname=TVar(name="foo"), args=[TUnit()])

    assert parse("def foo () = 1") == TDef(
        name=Token("CNAME", "foo"),
        args=[TUnit()],
        body=TBlock(exprs=[TInteger(value=1)]),
    )
    assert parse("foo.bar ()") == TApply(fname=TVar(name="foo.bar"), args=[TUnit()])
    assert parse("fun x => x") == TFun(args=[Token("CNAME", "x")], body=TVar(name="x"))

    assert parse("type x = int") == TyDecl(name="x", typ=TyConst(typ="int"))
    assert parse("type x = int -> string -> bool") == TyDecl(
        name="x",
        typ=TyArrow(
            t1=TyConst(typ="int"),
            t2=TyArrow(t1=TyConst(typ="string"), t2=TyConst(typ="bool")),
        ),
    )
    assert parse("type f = a -> b -> c") == TyDecl(
        name="f",
        typ=TyArrow(
            t1=TyVar(var="a"), t2=TyArrow(t1=TyVar(var="b"), t2=TyVar(var="c"))
        ),
    )
    assert parse("type f = (a -> b) -> c") == TyDecl(
        name="f",
        typ=TyArrow(
            t1=TyArrow(t1=TyVar(var="a"), t2=TyVar(var="b")), t2=TyVar(var="c")
        ),
    )


# Compiling stuff
def indent(i):
    return " " * i * 4


def compile_py_expr(ast) -> str:
    def compile(*_) -> NoReturn:  # type: ignore
        raise Exception("compile_py_expr must not call compile")

    if type(ast) is TBool:
        return "True" if ast.value else "False"
    elif type(ast) is TVar:
        return f"{ast.name}"
    elif type(ast) is TApply:
        fname = compile_py_expr(ast.fname)

        if len(ast.args) == 1 and type(ast.args[0]) is TUnit:
            return f"{fname}()"

        args = ", ".join(compile_py_expr(x) for x in ast.args)
        return f"{fname}({args})"
    elif type(ast) is TString:
        return repr(ast.value)
    elif type(ast) is TOp:
        return ast.op
    elif type(ast) is TInteger:
        return str(ast.value)
    elif type(ast) is TBin:
        return " ".join(compile_py_expr(n) for n in ast.values)
    elif type(ast) is TLet:
        e1 = compile_py_expr(ast.e1)
        e2 = compile_py_expr(ast.e2)
        return f"(lambda {ast.var} : {e2})({e1})"
    elif type(ast) is TIfElse:
        return f"{compile_py_expr(ast.then)} if {compile_py_expr(ast.cond)} else {compile_py_expr(ast.else_)}"
    elif type(ast) is TFun:
        body = compile_py_expr(ast.body)
        if len(ast.args) == 1 and type(ast.args[0]) is TUnit:
            return f"(lambda: {body})"
        else:
            return "(lambda {}: {})".format(", ".join(ast.args), body)  # type: ignore

    raise RuntimeError(f"Compile error, {ast} not known")


def compile(ast, i=0) -> str:
    if type(ast) is TLet:
        s = S()
        s.write(f"{indent(i)}{ast.var} = {compile(ast.e1, 0)}\n")
        s.write(f"{indent(i)}{compile(ast.e2, 0)}\n")
        return s.getvalue()
    elif type(ast) is TFromImport:
        return f"from {ast.module} import {','.join(ast.symbols)}\n"
    elif type(ast) is TImport:
        return f"import {ast.module}"
    elif type(ast) is TDef:
        s = S()
        s.write(indent(i))
        s.write(f"def {ast.name}")
        if len(ast.args) == 1 and type(ast.args[0]) is TUnit:
            s.write("():\n")
        else:
            s.write("(")
            s.write(", ".join(ast.args))  # type: ignore
            s.write("):\n")
            s.write(indent(i))

        exprs = [
            "{}{}".format(indent(i + 1), compile_py_expr(e))
            for e in ast.body.exprs[:-1]
        ]
        exprs.append(
            "{}return {}\n".format(indent(i + 1), compile_py_expr(ast.body.exprs[-1]))
        )
        s.write("\n".join(exprs))
        return s.getvalue()
    elif type(ast) is TScript:
        exprs = [compile(e) for e in ast.exprs]
        exprs_str = "\n".join(exprs)
        return exprs_str
    else:
        return indent(i) + compile_py_expr(ast)


def pcompile(inp):
    return compile(parse(inp))


def compile_opened_file(openf: TextIO) -> str:
    return pcompile(openf.read())


def prettify(fname):
    from subprocess import run

    try:
        run(["black", "-q", fname])
    except:
        pass


def compile_file(input: str, output: str):
    with open(input, "r") as i:
        out = compile_opened_file(i)
        if output == "-":
            print(out)
        else:
            with open(output, "w") as o:
                o.write(out)
            prettify(output)


def prun(inp):
    with NamedTemporaryFile("w", delete=False) as o:
        with open(inp, "r") as i:
            out = compile_opened_file(i)
        o.write(out)
        o.flush()
        cmdline = [sys.executable, o.name]
        run(cmdline)


def test_compile():
    assert pcompile("true") == "True"
    assert (
        pcompile("let x = true in x")
        == """\
x = True
x
"""
    )

    assert pcompile("from foo import bar tar zar") == "from foo import bar,tar,zar\n"

    assert (
        pcompile("def id x = x")
        == """\
def id(x):
    return x
"""
    )

    assert (
        pcompile("def foo x = let y = true in y")
        == """\
def foo(x):
    return (lambda y : y)(True)
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

    assert pcompile("f a b c") == "f(a, b, c)"
    assert pcompile("100 * 100 + 100") == "100 * 100 + 100"
    assert pcompile("foo ()") == "foo()"
    assert (
        pcompile("def foo () = 1")
        == """def foo():
    return 1
"""
    )
    assert pcompile("foo.bar ()") == "foo.bar()"

    assert pcompile("fun x => x") == "(lambda x: x)"


def main():
    argparser = ArgumentParser("Lampy 3")
    argparser.add_argument("command", metavar="CMD", type=str, help="One of [compile]")
    argparser.add_argument("--input")
    argparser.add_argument("--output", default="-")

    args = argparser.parse_args()

    if args.command == "compile":
        compile_file(args.input, args.output)
    elif args.command == "run":
        prun(args.input)


if __name__ == "__main__":
    main()
