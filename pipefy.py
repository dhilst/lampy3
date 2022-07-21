import sys
from functools import partial

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
    import importlib
    if m not in sys.modules:
        importlib.import_module(m)
    m = sys.modules[m]
    into = sys.modules[into]
    for k, v in m.__dict__.items():
        if (k[0].islower() and 'Error' not in k and callable(v) 
            and not k.startswith('__') and k not in blacklist):
            into.__dict__[k] = f(v)


patch_module('builtins', pipefy, __name__)
patch_module('functools', pipefy, __name__)
patch_module('operator', pipefy, __name__)

assert (range(1, 10) @ filter(lt(..., 5), ...) @        # type: ignore
        map(mul(2, ...), ...) @ list(...)) == [2,4,6,8] # type: ignore

class ExceptionMonad:
    blacklist = (AssertionError, NameError, ImportError, SyntaxError, MemoryError,
                 OverflowError, StopIteration, StopAsyncIteration, SystemError, Warning)
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

@pipefy        
def sub(a, b):
    result = a - b
    if result < 0:
        raise ValueError("underflow")
    return result

@pipefy
def add(a, b):
    return lakdfjald

assert (ExceptionMonad.ret(1) @ sub(..., 1) @ sub(..., 1)) == ValueError("underflow") 
assert (ExceptionMonad.ret(3) @ sub(..., 1) @ sub(..., 1)) == 1
