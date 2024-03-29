"Useful functional hacks"
import sys
from functools import partial, reduce
from dataclasses import make_dataclass

class Pipe:
    def __init__(self, f, *args, **kwargs):
        self.f = f
        self.args = args
        self.kwargs = kwargs
    def __call__(self, replacement):
        args = [arg if arg is not Ellipsis else replacement
                for arg in self.args]
        kwargs = {k: v if v is not Ellipsis else replacement
                  for arg in self.kwargs}
        return self.f(*args, **kwargs)
    def __rmatmul__(self, other):
        return self(other)

def pipefy(f):
    def wrapper(*args, **kwargs):
        if Ellipsis not in args and Ellipsis not in kwargs:
            return f(*args, **kwargs)
        else:
            return Pipe(f, *args, **kwargs)
    return wrapper

def patch_module(m, f, into, blacklist=[]):
    blacklist = blacklist + 'int str list tuple dict float bool type'.split()
    import importlib
    if m not in sys.modules:
        importlib.import_module(m)
    m = sys.modules[m]
    into = sys.modules[into]
    for k, v in m.__dict__.items():
        if (k[0].islower() and 'Error' not in k and callable(v) 
            and not k.startswith('__') and k not in blacklist):
            into.__dict__[k] = f(v)

def pipefy_builtins(mod):
    patch_module('functools', pipefy, mod)
    patch_module('operator', pipefy, mod)

filter = pipefy(filter) # type: ignore
map = pipefy(map) # type: ignore
reduce = pipefy(reduce) # type: ignore
list = pipefy(list) # type: ignore
pipefy_builtins(__name__)
reversed = pipefy(reversed)

def test_pipefy():
    assert (range(1, 10) @ filter(lt(..., 5), ...) @        # type: ignore
            map(mul(2, ...), ...) @ list(...)) == [2,4,6,8] # type: ignore

class ExceptionMonad:
    blacklist = (AssertionError, NameError, ImportError, SyntaxError, MemoryError,
                 OverflowError, StopIteration, StopAsyncIteration, SystemError, Warning,
                 AttributeError)
    def __init__(self, v):
        self.v = v

    def map(self, f):
        if isinstance(self.v, Exception):
            return self
        else:
            try:
                return ExceptionMonad(f(self.v))
            except Exception as e:
                if isinstance(e, self.blacklist):
                    raise
                return ExceptionMonad(e)

    def join(self, other):
        if isinstance(other, ExceptionMonad):
            return other.v
        else:
            return other

    def flatmap(self, other):
        return self.join(self.map(other))
    
    @staticmethod
    def ret(a):
        return ExceptionMonad(a)

    def __matmul__(self, other):
        return self.map(other)

    def __eq__(self, other):
        if isinstance(self.v, Exception) and isinstance(other, Exception):
            return (type(self.v), *self.v.args) == (type(other), *other.args)
        elif isinstance(self.v, Exception) and type(other) is ExceptionMonad and isinstance(other.v, Exception):
            return (type(self.v), *self.v.args) == (type(other.v), *other.v.args)
        elif isinstance(other, ExceptionMonad):
            return self.v == other.v
        else:
            return self.v == other

    def __repr__(self):
        return f"ExceptionMonad({self.v})"


def test_ExceptionMonad():
    @pipefy
    def sub(a, b):
        c = a - b
        if c < 0:
            raise ValueError("underflow")
        return c
    assert (ExceptionMonad.ret(1) @ sub(..., 1) @ sub(..., 1)) == ValueError("underflow") 
    assert (ExceptionMonad.ret(3) @ sub(..., 1) @ sub(..., 1)) == 1

def adt(datatype, *ctrs: str):
    basecls = type(datatype, (), {})
    klass = lambda x: x.split()[0]
    fields = lambda x: x.split()[1:]
    clss = (make_dataclass(klass(cls),
                           bases=(basecls,),
                           fields=list(fields(cls)),
                           frozen=True,
                           eq=True)
            for cls in ctrs)
    return (basecls, *clss)

class Data:
    def __init__(self, base):
        self.base = base
        self.ctrs = []
    def __or__(self, ctr):
        self.ctrs.append(ctr)
        return self
    def __gt__(self, ctr):
        self.ctrs.append(ctr)
        return adt(self.base, *self.ctrs)

def test_adt():
    Maybe, Just, Nothing = Data("Maybe") | "Just v" > "Nothing"
    assert isinstance(Just(1), Maybe)
    assert isinstance(Nothing(), Maybe)
