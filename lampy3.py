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
    tyarrow : tyatom (ARROW tyexpr_1)+

    block : expr_1 | (expr_1 ";")+

    def_            : "def"i CNAME ((CNAME+) | UNIT) (":" tyarrow)? "=" block "end"i?
    from_import     : "from"i qname "import"i qname+
    import_          : "import"i qname

    fun             : "fun"i (CNAME+ | UNIT) (":" tyarrow)? FAT_ARROW expr_1
    let             : "let"i CNAME (":" tyatom)? "=" expr_1 "in" expr_1
    ifelse          : "if"i expr_1 "then"i expr_1 "else"i expr_1 (":" tyatom)?
    bin_expr : expr_1 (OP expr_1)+ (":" tyatom)?
    ?appl : appl expr_3+ (":" tyatom)? | expr_3
    ?atom : "(" expr_1 ")"

    ?const : bool | ESCAPED_STRING -> string | INT -> integer | UNIT

    qname : CNAME ("." CNAME)*
    var : qname
    bool : BOOL

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
class TAST:
    pass


@Mixin.eq
class AST:
    parent: Optional["AST"] = None
    typ: Optional["TAST"] = None


@dataclass
class TyArrow(TAST):
    # @FIXME : this should be TAST and not str
    # arrows may contain arrows
    parms: List[str]



@dataclass
class TyConst(TAST):
    typ: str


@dataclass
class TyVar(TAST):
    var: str


@dataclass
class TApply(AST):
    func: AST
    args: List[AST]
    typ: Optional[TAST] = None

    def __post_init__(self):
        self.func.parent = self
        for arg in self.args:
            arg.parent = self.parent


@dataclass
class TUnit(AST):
    typ: TAST = TyConst("unit")


@dataclass
class TBool(AST):
    value: bool
    typ: TAST = TyConst("bool")


@dataclass
class TLet(AST):
    var: str
    e1: AST
    e2: AST
    typ: Optional[TAST] = None

    def __post_init__(self):
        self.e1.parent = self
        self.e2.parent = self


@dataclass
class TString(AST):
    value: str
    typ: TAST = TyConst("string")


@dataclass
class TInteger(AST):
    value: int
    typ: TAST = TyConst("int")


@dataclass
class TVar(AST):
    name: str
    typ: Optional[TAST] = None


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
    typ: Optional[TAST] = None

    def __post_init__(self):
        for expr in self.exprs:
            expr.parent = self


@dataclass
class TDef(AST):
    name: str
    args: Union[List[TUnit], List[str]]
    body: TBlock
    typ: Optional[TAST] = None

    def __post_init__(self):
        self.body.parent = self
        for arg in self.args:
            if isinstance(arg, AST):
                arg.parent = self


@dataclass
class TFun(AST):
    args: Union[List[TUnit], List[str]]
    body: AST
    typ: Optional[TAST] = None

    def __post_init__(self):
        self.body.parent = self


@dataclass
class TIfElse(AST):
    cond: AST
    then: AST
    else_: AST
    typ: Optional[TAST] = None

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
    typ: Optional[TAST] = None

    def __post_init__(self):
        for v in self.values:
            v.parent = self


@dataclass
class TOp(AST):
    op: str


class Transmformator(LarkTransformer):
    def __init__(self):
        self.statements = []

    def UNIT(self, tree):
        return TUnit()

    def tyvar(self, tree):
        return TyVar(tree[0].value)

    def tyarrow(self, tree):
        t1, _, t2 = tree
        if type(t2) is TyArrow:
            return TyArrow([t1, *t2.parms])
        else:
            return TyArrow([t1, t2])

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

    def def_(self, tree):
        name, *args, body = tree
        args = list(a.value if type(a) is Token else a for a in args)
        if isinstance(args[-1], TAST):
            typ = args.pop()
            return TDef(name.value, args, body, typ)
        else:
            return TDef(name.value, args, body)

    def fun(self, tree):
        if len(tree) == 4:
            *args, typ, _, body = tree
            args = list(a.value if type(a) is Token else a for a in args)
            return TFun(args, body, typ)
        else:
            *args, _, body = tree
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

    is_ast("fun foo x => x")
    is_ast("def foo x : int -> int = if x == 0 then 0 else 1")


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

    assert parse("foo ()") == TApply(func=TVar(name="foo"), args=[TUnit()])

    assert parse("def foo () = 1") == TDef(
        name=Token("CNAME", "foo"),
        args=[TUnit()],
        body=TBlock(exprs=[TInteger(value=1)]),
    )
    assert parse("foo.bar ()") == TApply(func=TVar(name="foo.bar"), args=[TUnit()])
    assert parse("fun x => x") == TFun(args=[Token("CNAME", "x")], body=TVar(name="x"))

    # type declarations
    assert parse("fun x : int -> int => x") == TFun(
        args=[Token("CNAME", "x")],
        body=TVar(name="x"),
        typ=TyArrow(parms=[TyConst(typ="int"), TyConst(typ="int")]),
    )

    assert parse("let x : int = 1 in x") == TLet(
        var=Token("CNAME", "x"),
        e1=TInteger(value=1, typ=TyConst(typ="int")),
        e2=TVar(name="x", typ=None),
        typ=TyConst(typ="int"),
    )

    assert parse("def foo () : unit -> int = 1") == TDef(
        name=Token("CNAME", "foo"),
        args=[TUnit()],
        body=TBlock(exprs=[TInteger(value=1)]),
        typ=TyArrow(parms=[TyConst(typ="unit"), TyConst(typ="int")]),
    )

    assert parse("if true then false else true : bool") == TIfElse(
        TBool(True), TBool(False), TBool(True), TyConst(typ="bool")
    )

    assert parse("(if true then false else true : bool)") == TIfElse(
        TBool(True), TBool(False), TBool(True), TyConst(typ="bool")
    )


def error(*args, **kwargs) -> bool:
    print(*args, file=sys.stderr, **kwargs)
    return False

# only for testing
def _arrow(text):
    tokens = [x for x in text.split() if x != "->"]
    return TyArrow(tokens)

def test_parsearrow():
    assert _arrow("a -> b -> c") == TyArrow("a b c".split())

def subst_types(x: str, by: str, ast: TAST) -> TAST:
    if type(ast) is TyConst:
        return ast
    elif type(ast) is TyVar:
        return TyVar(by) if ast.var == x else ast # type: ignore
    elif type(ast) is TyArrow:
        return TyArrow([(by if p == x else p) for p in ast.parms]) # type: ignore
    else:
        raise TypeError(f"Unknow TAST {ast}")

def test_subst_types():
    assert subst_types("x", "y", TyConst("bool")) == TyConst("bool")
    assert subst_types("x", "y", TyVar("z")) == TyVar("z")
    assert subst_types("x", "y", TyVar("x")) == TyVar("y")
    assert subst_types("x", "y", _arrow("x -> y")) == _arrow("y -> y")
    assert subst_types("x", "y", _arrow("a -> a")) == _arrow("a -> a")

def normalize_arrow(a1: TyArrow, a2: TyArrow) -> Optional[TyArrow]:
    if len(a1.parms) == len(a2.parms):
        for a1arg, a2arg in zip(a1.parms, a2.parms):
            a2 = cast(TyArrow, subst_types(a2arg, a1arg, a2)) # this is wrong
        return a2
    return None

def test_normalize_arrow():
    assert normalize_arrow(_arrow("a -> b"), _arrow("c -> d")) == _arrow("a -> b")
    assert normalize_arrow(_arrow("a -> b"), _arrow("b -> a")) == _arrow("a -> b") # oops
    # i need real alpha conversion

def unify_types(t1: TAST, t2: TAST) -> bool:
    if type(t1) is TyConst and type(t2) is TyConst:
        return t1.typ == t2.typ  # type: ignore
    elif type(t1) is TyVar and type(t2) is TyConst:
        return True
    elif type(t1) is TyConst and type(t2) is TyVar:
        return True
    elif type(t1) is TyVar and type(t2) is TyVar:
        return t1.var == t2.var  # type: ignore
    elif type(t1) is TyArrow and type(t2) is TyArrow:
        # this is wrong because
        # unify a -> a, b -> b is false
        # and should be true
        return len(t1.parms) == len(t2.parms) and all(  # type: ignore
            unify_types(t1_, t2_) for t1_, t2_ in zip(t1.parms, t2.parms)  # type: ignore
        )
    else:
        return False


def test_unify_types():
    assert unify_types(TyVar("a"), TyVar("a"))
    assert unify_types(TyVar("a"), TyConst("int"))
    assert unify_types(TyConst("int"), TyVar("a"))
    assert unify_types(
        TyArrow([TyVar("a"), TyVar("a")]), TyArrow([TyVar("a"), TyVar("a")])
    )
    assert unify_types(TyConst("int"), TyConst("int"))
    assert unify_types(TyConst("int"), TyConst("bool")) == False
    assert unify_types(TyArrow([TyVar("a"), TyVar("a")]), TyConst("int")) == False
    assert unify_types(TyConst("int"), TyArrow([TyVar("a"), TyVar("a")])) == False


@no_type_check
def compile_typecheck(ast: AST, env: frozendict) -> Tuple[bool, frozendict]:
    if type(ast) is TScript:
        newenv = env
        for expr in ast.exprs:
            result, newenv = compile_typecheck(expr, newenv)
            if result == False:
                return False, env
    elif type(ast) is TApply:
        if type(ast.func) is TVar:
            ftype = env.get(ast.func.name)
            if ftype is None:
                return error(f"Couldn't find type for function {ast.func.name}"), env
        elif type(ast.func) is TFun:
            ftype = ast.func.typ
        else:
            assert False, env

        assert type(ftype) is TyArrow
        parms, args = ftype.parms[:-1], ast.args
        largs, lparms = len(args), len(parms)
        if largs > lparms:
            return error(f"To many arguments expected {lparms} found {largs}"), env
        pairs = zip(parms, (arg.typ for arg in args))
        for t1, t2 in pairs:
            if t1 is None:
                return error(f"Type anotation is None, can't type check in parameters")
            elif t2 is None:
                error(f"None in type of arguments {args}")
                return error(f"Type anotation is None, can't type check in arguments")
            if unify_types(t1, t2) == False:
                return error(f"Expecting type {t1}, found {t2}"), env
        return True, env
    elif type(ast) is TDef:
        return True, env.set(ast.name, ast.typ)
    elif type(ast) is TFun:
        if ast.typ is None:
            return error(f"None type in anonymous function"), env
        argtyp_dict = {k: v for k, v in zip(ast.args, ast.typ.parms[:-1])}  # type: ignore
        return compile_typecheck(ast.body, env | argtyp_dict)
    elif type(ast) is TIfElse:
        if ast.cond.typ != TyConst("bool"):
            return error(f"Expected bool expression on if condition {ast}"), env

        if ast.then.typ != ast.else_.typ:
            return (
                error(
                    f"'then' and 'else' types doesn't match in the if expression {ast}"
                ),
                env,
            )
        return True, env
    elif type(ast) is TBin:
        a, op, b = ast.values
        if not compile_typecheck(a, env)[0]:
            return False, env
        elif not compile_typecheck(b, env)[0]:
            return False, env
        elif a.typ is None or b.typ is None:
            return error("None type in binary expression"), env
        elif a.typ != b.typ:
            return error(f"Expected {a.typ} but found {b.typ}"), env
        else:
            ast.typ = a.typ
            return True, env
    elif type(ast) is TLet:
        typ = ast.typ if ast.typ is not None else ast.e1.typ
        return compile_typecheck(ast.e2, env | {ast.var: typ})
    elif type(ast) in (TBool, TVar, TImport, TFromImport, TInteger):
        return True, env

    return error(f"Unexpected node {ast}"), env


def test_typechecker():
    assert (
        compile_typecheck(parse('def id x : int -> int = x;; id "foo";'), frozendict())[
            0
        ]
        == False
    )
    assert (
        compile_typecheck(
            parse('fun id : (int -> int) -> int => id "foo"'),
            frozendict(),
        )[0]
        == False
    )
    assert (
        compile_typecheck(
            parse('fun id : (a -> a) -> a => id "foo"'),
            frozendict(),
        )[0]
        == True
    )
    assert (
        compile_typecheck(
            parse(
                """def test_id id : (a -> a) -> unit =
                     id "foo";
                     id 1;
                     ();;
                """
            ),
            frozendict(),
        )[0]
        == True
    )


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


def pcompile(inp, typecheck=True):
    ast = parse(inp)
    if typecheck:
        welltyped, _ = compile_typecheck(ast, frozendict())
        if not welltyped:
            raise RuntimeError("Typecheck error")
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

    assert pcompile("f a b c", False) == "f(a, b, c)"
    assert pcompile("100 * 100 + 100") == "100 * 100 + 100"
    assert pcompile("foo ()", False) == "foo()"
    assert (
        pcompile("def foo () = 1")
        == """def foo():
    return 1
"""
    )
    assert pcompile("foo.bar ()", False) == "foo.bar()"

    assert pcompile("fun x => x", False) == "(lambda x: x)"


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
