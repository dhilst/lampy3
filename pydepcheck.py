import sys
import inspect
import importlib
from ast import *

def try_(func, *args, **kwargs):
    try:
        return func(*args, **kwargs), None
    except Exception as e:
        return  None, e

class Typer(NodeTransformer):
    def __init__(self, module_name, source, typeenv={}):
        self.mod = importlib.import_module(module_name.replace(".py", ""))
        self.modname = module_name
        self.typeenv = typeenv
        self.source = source

    def eval(self, node):
        return eval(compile(fix_missing_locations(Expression(node)), self.modname, "eval"), vars(self.mod))

    # def visit_Assign(self, node):
    #     if len(node.targets) == 1:
    #         name = node.targets[0].id
    #         if type(node.value) is Constant:
    #             typ = type(node.value.value)
    #         elif type(node.value) is Call and type(node.value.func) is Name:
    #             if node.value.func.id is "prop":
    #                 typ = type
    #             else:
    #                 typ = self.eval(node.value.func)
    #         self.typeenv[name] = typ
    
    def calc_ret_type(self, typ):
        if typ is None:
            return None
        elif callable(typ):
            return typ()
        else:
            return typ

    def get_source(self, node):
        return get_source_segment(self.source, node)

    def visit_Call(self, node):
        if node.func.id == "typedebug":
            print(*(arg.value for arg in node.args))
            return node

        elif node.func.id == "type_":
            name = node.args[0].value
            typ = node.args[1]
            self.typeenv[name] = typ
            return node

        elif type(node.func) is Name:
            if node.func.id not in self.typeenv:
                # print(f"Warning : No type information for {node.func.id}")
                return node

            typ = self.typeenv[node.func.id]
            nparms = len(typ.args.args)
            typargs = node.args[:nparms]
            reduced_typs = self.eval(Call(typ, typargs, keywords=[]))
            nodeargs = [self.visit(arg) for arg in node.args]
            fargs, err = try_(self.eval, Tuple(nodeargs, Load()))
            if err is not None:
                print(f"Type error at {self.get_source(node)} : {err}")
                return node
            
            for typ, term in zip(reduced_typs, fargs):
                # type(typ) is P do not work here, Python thinks that the imported P
                # in the module is different from this P, even if it's the same
                # I think this is because I import the module here, as workaround
                # I use the module's P to test
                if type(typ) is vars(self.mod).get('P'):
                    if not isinstance(term, typ):
                        print(f"Type error at {self.get_source(node)} : Not an instance of {typ}")
                elif type(term) is not typ:
                    print(f"Type error at {self.get_source(node)} : Got {type(term).__name__}, while expecting {typ.__name__}")
                    # sys.exit(-1)

            rettyp = self.calc_ret_type(reduced_typs[-1])
            return Constant(rettyp)

        return node

def typecheck(module_name):
    code = open(module_name).read()
    tree = parse(code)
    Typer(module_name, code).visit(tree)


def type_(name, typ):
    pass

def typedebug(*args):
    pass

def prop(name, pred):
    def __init__(self, *args):
        if not pred(*args):
            raise TypeError(f"{args} is not a valid {name}")
        self.val = args
        self.pred = pred

    return type(name, tuple(), {'__init__': __init__})

class P:
    def __init__(self, p):
        self.p = p

    def __instancecheck__(self, other):
        return self.p(other)

    def __repr__(self):
        return f"P({repr(self.p)}"

if __name__ == '__main__':
    typecheck(sys.argv[1])
