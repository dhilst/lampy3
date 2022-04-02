import sys
import re
from copy import deepcopy, copy
from argparse import ArgumentParser
from tempfile import NamedTemporaryFile
from subprocess import run
from typing import *
from dataclasses import dataclass, fields, is_dataclass
from lark import Lark, Transformer as LarkTransformer, Token, Discard
from io import StringIO as S
from functools import partial
from frozendict import frozendict  # type: ignore

A = TypeVar("A")
B = TypeVar("B")
C = TypeVar("C")
D = TypeVar("D")

grammar = r"""
    start : script
    ?script : stmt | (stmt ";")+

    ?stmt : def_ | import_ | from_import | expr_1
    ?expr_1 : let | ifelse | bin_expr | fun | expr_2
    ?expr_2 : appl
    ?expr_3 :  var | const | atom

    type_ : "type"i CNAME "="i tyexpr_1
    ?tyexpr_1 : tyatom | tyarrow
    ?tyatom : tyconst | tyvar | "(" tyexpr_1 ")"
    !tyvar : VAR_T
    !tyconst : INT_T | BOOL_T | STRING_T | UNIT_T
    tyarrow_2 : tyatom (ARROW tyexpr_1)+
    tyarrow : forall tyarrow_2+
    forall : "forall"i CNAME* ","i
    opt_tyarrow : (":" tyarrow)
    opt_tyatom : (":" tyatom)

    block : expr_1 | (expr_1 ";")+


    from_import     : "from"i qname "import"i qname+
    import_         : "import"i qname

    def_            : "def"i CNAME parms opt_tyarrow  "=" block "end"i?
    fun             : "fun"i parms opt_tyarrow "=>" expr_1

    let             : "let"i CNAME opt_tyatom "=" expr_1 "in" expr_1
    ifelse          : "if"i expr_1 "then"i expr_1 "else"i expr_1
    bin_expr : expr_1 (OP expr_1)+
    ?appl : appl expr_3+ | expr_3
    ?atom : "(" expr_1 ")"

    parms           : CNAME+ | UNIT

    ?const : bool | ESCAPED_STRING -> string | INT -> integer | UNIT

    qname : CNAME ("." CNAME)*
    var : qname
    bool : BOOL

    COLON : ":"
    UNIT : "()"
    VAR_T : /[a-z]/
    INT_T.30  : "int"
    BOOL_T.30 : "bool"
    STRING_T.30 : "string"
    UNIT_T.30 : "unit"
    FAT_ARROW.30 : "=>"
    ARROW.30 : "->"
    OP.10 : "*" | "+" | "-" | "/" | ">=" | "<=" | "==" | "!=" | ">" | "<"
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


dataclass = partial(dataclass, eq=False)  # type: ignore


class Mixin:
    # This is injected in another class
    @staticmethod
    def _eq(self_, other):
        if type(self_) != type(other):
            return False

        for kself in self_.__dict__.keys():
            if kself == "parent":
                continue

            if self_.__dict__[kself] != other.__dict__.get(kself):
                return False

        return True

    @staticmethod
    def eq(klass):
        setattr(klass, "__eq__", Mixin._eq)
        return klass


@Mixin.eq
class AST:
    parent: Optional["AST"] = None
    typ: Optional["AST"] = None


@dataclass
class TyArrow(AST):
    args: List[AST]
    forall: Set[str]


@dataclass
class TyConst(AST):
    typ: str  # type: ignore
    # @TODO make a base class for typed nodes


@dataclass
class TyVar(AST):
    var: str


@dataclass
class TApply(AST):
    func: AST
    args: List[AST]
    typ: Optional[AST] = None

    def __post_init__(self):
        self.func.parent = self
        for arg in self.args:
            arg.parent = self.parent


@dataclass
class TUnit(AST):
    typ: AST = TyConst("unit")


@dataclass
class TBool(AST):
    value: bool
    typ: AST = TyConst("bool")


@dataclass
class TLet(AST):
    var: str
    e1: AST
    e2: AST
    typ: Optional[AST] = None

    def __post_init__(self):
        self.e1.parent = self
        self.e2.parent = self


@dataclass
class TString(AST):
    value: str
    typ: AST = TyConst("string")


@dataclass
class TInteger(AST):
    value: int
    typ: AST = TyConst("int")


@dataclass
class TVar(AST):
    name: str
    typ: Optional[AST] = None


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
    typ: Optional[AST] = None

    def __post_init__(self):
        for expr in self.exprs:
            expr.parent = self


@dataclass
class TDef(AST):
    name: str
    args: Union[List[TUnit], List[str]]
    body: TBlock
    typ: Optional[AST] = None

    def __post_init__(self):
        self.body.parent = self
        for arg in self.args:
            if isinstance(arg, AST):
                arg.parent = self


@dataclass
class TFun(AST):
    args: Union[List[TUnit], List[str]]
    body: AST
    typ: Optional[AST] = None

    def __post_init__(self):
        self.body.parent = self


@dataclass
class TIfElse(AST):
    cond: AST
    then: AST
    else_: AST
    typ: Optional[AST] = None

    def __post_init__(self):
        self.cond.parent = self
        self.then.parent = self
        self.else_.parent = self


@dataclass
class TScript(AST):
    exprs: List[AST]

    def __post_init__(self):
        for expr in self.exprs:
            expr.parent = self


@dataclass
class TBin(AST):
    values: List[AST]
    typ: Optional[AST] = None

    def __post_init__(self):
        for v in self.values:
            v.parent = self


@dataclass
class TOp(AST):
    op: str


def find(x, l):
    "like l.index, but without exception"
    try:
        return l.index(x)
    except ValueError:
        return None


class Transmformator(LarkTransformer):
    def __init__(self):
        self.statements = []

    def UNIT(self, tree):
        return TUnit()

    def tyvar(self, tree):
        return TyVar(tree[0].value)

    def forall(self, tree):
        return {t.value for t in tree}

    def tyarrow_2(self, tree):
        print("tyarrow_2", tree)
        return [v for v in tree if v != Token("ARROW", "->")]

    def tyarrow(self, tree):
        print(tree)
        forall, args = tree
        return TyArrow(args, forall)

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
        if len(tree) == 3:
            v, e1, e2 = tree
            return TLet(v.value if type(v) is Token else v, e1, e2)
        else:
            v, typ, e1, e2 = tree
            return TLet(v.value if type(v) is Token else v, e1, e2, typ)

    def import_(self, tree):
        return TImport(tree[0])

    def from_import(self, tree):
        return TFromImport(tree[0], tree[1:])

    def qname(self, tree):
        return ".".join(tree)

    def block(self, tree):
        return TBlock(tree)

    def parms(self, tree):
        return [t.value if type(t) is Token else t for t in tree]

    def opt_tyatom(self, tree):
        return tree[0] if len(tree) > 0 else None

    def opt_tyarrow(self, tree):
        return tree[0] if len(tree) > 0 else None

    def def_(self, tree):
        name, args, typ, body = tree
        return TDef(name.value, args, body, typ)

    def fun(self, tree):
        args, typ, body = tree
        return TFun(args, body, typ)

    def ifelse(self, tree):
        return TIfElse(*tree)

    def appl(self, tree):
        fname, *args = tree
        return TApply(fname, args)

    def script(self, tree):
        return TScript(tree)

    def bin_expr(self, tree):
        values: List[AST] = []
        for t in tree:  # exclude the type
            if type(t) is Token and t.type == "OP":
                values.append(TOp(t.value))
            elif isinstance(t, AST):
                values.append(t)
            else:
                raise TypeError(f"Unexpected type at {t}")

        return TBin(values)


def topdown_iter(x: AST) -> Iterable[AST]:
    if is_dataclass(x) and isinstance(x, AST):
        yield x
        for f in fields(x):
            if f.name == "parent":
                continue
            attr = getattr(x, f.name)
            yield from topdown_iter(attr)
    elif isinstance(x, list):
        for y in x:
            yield from topdown_iter(y)


def bottomup_iter(x: AST) -> Iterable[AST]:
    if is_dataclass(x) and isinstance(x, AST):
        for f in fields(x):
            if f.name == "parent":
                continue
            attr = getattr(x, f.name)
            yield from bottomup_iter(attr)
        yield x
    elif isinstance(x, list):
        for y in x:
            yield from bottomup_iter(y)


def test_iter():
    def is_ast(code: str):
        assert all(isinstance(x, AST) for x in topdown_iter(parse(code)))
        assert all(isinstance(x, AST) for x in bottomup_iter(parse(code)))

    is_ast("fun foo x : forall a, a -> a => x")
    is_ast("def foo x : forall, int -> int = if x == 0 then 0 else 1")


def ast_transform(ast: AST, f: Callable[[AST], AST]):
    if type(ast) is TScript:
        return f(TScript([f(e) for e in ast.exprs]))
    elif type(ast) is TDef:
        return f(
            TDef(
                ast.name,
                ast.args,
                cast(TBlock, f(ast.body)),
                f(ast.typ) if ast.typ is not None else None,
            )
        )
    elif type(ast) is TBlock:
        return f(TBlock([f(e) for e in ast.exprs]))
    elif type(ast) is TBin:
        return f(TBin([f(v) for v in ast.values]))
    elif type(ast) is TFun:
        return f(
            TFun(ast.args, f(ast.body), f(ast.typ) if ast.typ is not None else None)
        )
    else:
        return f(ast)


def test_parse():
    assert parse("true") == TBool(True)
    assert parse("false") == TBool(False)
    assert parse("let x : bool = true in x") == TLet(
        var="x",
        e1=TBool(value=True, typ=TyConst(typ="bool")),
        e2=TVar(name="x", typ=None),
        typ=TyConst(typ="bool"),
    )
    assert parse("from foo import bar tar zar") == TFromImport(
        "foo", "bar tar zar".split()
    )

    assert parse("def id x : forall a, a -> a = x end") == TDef(
        name="id",
        args=["x"],
        body=TBlock(exprs=[TVar(name="x", typ=None)], typ=None),
        typ=TyArrow([TyVar(var="a"), TyVar(var="a")], forall={"a"}),
    )
    assert parse("def const a b : forall a b, a -> b -> a = a end") == TDef(
        name="const",
        args=["a", "b"],
        body=TBlock(exprs=[TVar(name="a", typ=None)], typ=None),
        typ=TyArrow(
            args=[TyVar(var="a"), TyVar(var="b"), TyVar(var="a")], forall={"a", "b"}
        ),
    )

    assert parse("if true then false else true") == TIfElse(
        TBool(True), TBool(False), TBool(True)
    )

    assert parse("foo foo") == TApply(
        func=TVar(name="foo", typ=None), args=[TVar(name="foo", typ=None)], typ=None
    )
    assert parse("foo foo foo") == TApply(TVar("foo"), [TVar("foo"), TVar("foo")])

    assert parse('"foo"') == TString("foo")
    assert parse("100") == TInteger(100)
    assert parse("100 * 100") == TBin([TInteger(100), TOp("*"), TInteger(100)])

    assert parse("foo ()") == TApply(func=TVar(name="foo"), args=[TUnit()])

    assert parse("def foo () : forall, unit -> int = 1") == TDef(
        name="foo",
        args=[TUnit(typ=TyConst(typ="unit"))],
        body=TBlock(exprs=[TInteger(value=1, typ=TyConst(typ="int"))], typ=None),
        typ=TyArrow(args=[TyConst(typ="unit"), TyConst(typ="int")], forall=set()),
    )
    assert parse("foo.bar ()") == TApply(func=TVar(name="foo.bar"), args=[TUnit()])
    assert parse("fun x : forall, int -> int => x") == TFun(
        args=["x"],
        body=TVar(name="x", typ=None),
        typ=TyArrow(args=[TyConst(typ="int"), TyConst(typ="int")], forall=set()),
    )

    # type declarations
    assert parse("fun x : forall, int -> int => x") == TFun(
        args=["x"],
        body=TVar(name="x"),
        typ=TyArrow([TyConst(typ="int"), TyConst(typ="int")], set()),
    )

    assert parse("let x : int = 1 in x") == TLet(
        var="x",
        e1=TInteger(value=1, typ=TyConst(typ="int")),
        e2=TVar(name="x", typ=None),
        typ=TyConst(typ="int"),
    )

    assert parse("def foo () : forall, unit -> int = 1") == TDef(
        name="foo",
        args=[TUnit()],
        body=TBlock(exprs=[TInteger(value=1)]),
        typ=TyArrow([TyConst(typ="unit"), TyConst(typ="int")], forall=set()),
    )

    assert parse("if true then false else true") == TIfElse(
        TBool(True), TBool(False), TBool(True), None
    )

    assert parse("(if true then false else true)") == TIfElse(
        TBool(True), TBool(False), TBool(True), None
    )

    assert parse("fun x y : forall a b, a -> b -> a => x") == TFun(
        args=["x", "y"],
        body=TVar(name="x", typ=None),
        typ=TyArrow(
            [TyVar(var="a"), TyVar(var="b"), TyVar(var="a")],
            forall={"a", "b"},
        ),
    )

    assert parse(
        "fun id : forall, (forall a, a -> a) -> (forall b, b -> b) => id"
    ) == TFun(
        args=["id"],
        body=TVar(name="id", typ=None),
        typ=TyArrow(
            args=[
                TyArrow(args=[TyVar(var="a"), TyVar(var="a")], forall={"a"}),
                TyArrow(args=[TyVar(var="b"), TyVar(var="b")], forall={"b"}),
            ],
            forall=set(),
        ),
    )

    assert parse("f a b c") == TApply(
        func=TVar(name="f", typ=None),
        args=[
            TVar(name="a", typ=None),
            TVar(name="b", typ=None),
            TVar(name="c", typ=None),
        ],
        typ=None,
    )


def error(*args, **kwargs) -> bool:
    print(*args, file=sys.stderr, **kwargs)
    return False


def compile_py_expr(ast) -> str:
    def compile(*_) -> NoReturn:  # type: ignore
        raise Exception("compile_py_expr must not call compile")

    if type(ast) is TBool:
        return "True" if ast.value else "False"
    elif type(ast) is TVar:
        return f"{ast.name}"
    elif type(ast) is TApply:
        fname = compile_py_expr(ast.func)

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


# Compiling stuff
def indent(i):
    return " " * i * 4


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
    ast = parse(inp)
    return compile(ast)


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
        pcompile("let x : bool = true in x")
        == """\
x = True
x
"""
    )

    assert pcompile("from foo import bar tar zar") == "from foo import bar,tar,zar\n"

    assert (
        pcompile("def id x : forall a, a -> a  = x")
        == """\
def id(x):
    return x
"""
    )

    assert (
        pcompile("def foo x : forall a, a -> bool = let y : bool = true in y")
        == """\
def foo(x):
    return (lambda y : y)(True)
"""
    )

    assert pcompile("if true then false else true") == "False if True else True"

    assert (
        pcompile("let x : bool = true in let y : bool = false in z")
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
        pcompile("def foo () : forall, unit -> int = 1")
        == """def foo():
    return 1
"""
    )
    assert pcompile("foo.bar ()") == "foo.bar()"

    assert pcompile("fun x : forall a, a -> a => x") == "(lambda x: x)"


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
