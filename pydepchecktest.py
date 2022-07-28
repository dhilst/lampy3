# type: ignore
from pydepcheck import type_, P

type_("id", lambda T: (type, T, T))
def id(T, a):
    return a

def test_id():
    id(int, 1)
    id(int, "foo")
    id(int, id(int, 1))

type_("add", lambda: (int, int, int))
def add(a, b):
    return a + b

def test_add():
    add(1, 2)
    add(1, True)
    add(1, "bar")
    add(1, add(2, 3))
    add(1, id(str, "foo"))

type_("accepts_nat", lambda: (P(lambda n: n >= 0), int))
def accepts_nat(n):
    return n

def test_accepts_nat():
    accepts_nat(1)
    accepts_nat(-1)
