# # type: ignore
from pydepcheck import type_, Type, Record, try_

type_("id", lambda T: (type, T, T))
def id(T, a):
    return a

def test_id():
    assert id(int, 1) == 1
    assert id(int, "foo") == "foo"
    assert id(int, id(int, 1)) == 1

type_("add", lambda: (int, int, int))
def add(a, b):
    return a + b

def test_add():
    assert add(1, 2) == 3
    assert add(1, True) == 2 
    try:
        add(1, "bar")
        assert False
    except TypeError:
        pass

    assert add(1, add(2, 3)) == 6

    try:
        add(1, id(str, "foo"))
        assert False
    except TypeError:
        pass


# Type is the type of the types, is like the bulitin python function
# `type` but more general. `int`, `float`, `bool` are valid `Type`s,
# and also complex types like the `box(T)` below

# defines a generic box(T) type
type_("box", lambda T: (Type, Type))
def box(T): return Type(box, T)

# receives a T and return a box(T)
type_("put_into_a_box", lambda T: (Type, T, box(T)))
def put_into_a_box(T, i):
    return [i]

# receives a box(int) and return an int
type_("get_from_a_box", lambda: (box(int), int))
def get_from_a_box(b):
    return b[0]

def test_box():
    # insert 1 in a box(int) and then remove it
    # int is the type parameter
    assert get_from_a_box(put_into_a_box(int, 1)) == 1


# Receives a (T : Type) and return a the nat(T) type
type_("nat", lambda: (Type, Type))
def nat(T):
    return Record({
        "type": T,
        "zero": T,
        "succ": lambda: (T, T)
    })

# Receives a (T: Type) (zero : T) (succ : T -> T) and returns
# a nat(T) term
type_("pack_nat", lambda T: (Type, T, lambda: (T, T), nat(T)))
def pack_nat(T, zero, succ):
    return {"type": T, "zero": zero, "succ": succ}

# inc knows nothing about T, just that it can call
# nat(T) functions on it, i.e, T is abstract 
# receives a (T : Type), (nat : nat(T)) (i : T) and
# returns a T
type_("inc", lambda T: (Type, nat(T), T, T))
def inc(T, nat, i):
    return nat["succ"](i)

# increment an int
type_("add1", lambda: (int, int))
def add1(a):
     return a + 1

def test_nat():
    # packs (int, 0, add1) into a nat(int) and pass it to
    # the inc function
    assert inc(int, pack_nat(int, 0, add1), 1) == 2


