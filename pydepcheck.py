import sys
import inspect
import importlib
from ast import *

unk = object()
unit = object()
function = type(lambda:None)
builtins = vars(sys.modules['builtins'])

class Type:
    def __init__(self, *args):
        self.args = args

    @staticmethod
    def is_a_type(other):
        return other in {int, float, bool, tuple, list, float, dict, function, unit, unk} or type(other) is Type or type(other) is type

    def __repr__(self):
        args = ", ".join(str(arg) for arg in self.args)
        return f"Type({args})"

    def __eq__(self, other):
        if type(other) is not Type:
            return False

        for arg, oarg in zip(self.args, other.args):
            if type(arg) is function:
                if not arg is oarg:
                    return False
            elif arg != oarg:
                return False
        return True


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

    def calc_ret_type(self, typ):
        if typ is None:
            return None
        elif callable(typ):
            return typ()
        else:
            return typ

    def get_source(self, node):
        return get_source_segment(self.source, node)

    def totype(self, node):
        if type(node) is Name:
            if node.id in self.typeenv:
                return self.typeenv[node.id]
            elif node.id in builtins:
                return builtins[node.id]
            else: 
                print(f"Error : No type information for {node.id}")
                return unk
        elif type(node) is Constant:
            return node.value

    def visit_Call(self, node):
        if node.func.id == "typedebug":
            for arg in node.args:
                if type(arg) is Constant:
                    print(arg.value, end=" ")
                elif type(arg) is Name:
                    print(f"{arg.id} : {type(self.totype(arg))}", end=" ")
                elif type(arg) is Call:
                    t = self.visit(arg)
                    print(f"{t.value} :- {type(self.totype(t))}", end=" ")
                else:
                    print(dump(arg))
            else:
                return
            
            print("")
                  
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
            
            for typ, term in zip(reduced_typs, nodeargs):
                term_ = self.totype(term)
                if typ is self.mod.Type:
                    if not Type.is_a_type(term_):
                        print(f"Error 01 in {node.func.id} @ {self.get_source(node)} : Expected {typ}, found {term_}")
                elif type(typ) is self.mod.Type:
                    if term_ != typ:
                        print(f"Error 02 in {node.func.id} @ {self.get_source(node)} : Expected {typ}, found {term_}")
                elif type(term_) is not typ:
                    print(f"Error 03 in {node.func.id} @ {self.get_source(node)} : Expected {typ}, found {type(term_)}")

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

if __name__ == '__main__':
    typecheck(sys.argv[1]) 
