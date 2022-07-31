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


type_("tlist", lambda T: (Type, Type))
def tlist(T):
    return Type(tlist, T)

type_("cons", lambda T: (Type, T, tlist(T), tlist(T)))
def cons(T, x, l):
    return [x, *l]

type_("nil", lambda T: (Type, tlist(T)))
def nil(T):
    return []

type_("mklist", lambda T: (Type, list, tlist(T)))
def mklist(T, l):
    return l

def test_tlist():
    assert cons(str, "a", cons(str, "b", nil(str))) == ["a", "b"]
    assert mklist(int, [1,2,3]) == [1,2,3]

type_("vec", lambda T: (Type, int, Type))
def vec(T, i):
    return Type(vec, T, i)

type_("mkvec", lambda T, l: (Type, tlist(T), vec(T, len(l))))
def mkvec(T, l):
    return l

type_("vunpack", lambda T, n: (Type, int, vec(T, n), tlist(T)))
def vunpack(T, n, vec):
    return vec

type_("vcons", lambda T, n: (Type, int, T, vec(T, n), vec(T, n + 1)))
def vcons(T, n, x, vec_):
    return [x, *vec_]

type_("head", lambda T: (Type, vec(T, 1), T))
def head(T, vec):
    return vec[0]

def test_tvec():
    # we have dependent type checking but only because these lists
    # exists statically, if they are created in runtime we will have
    # no enough information to reduce the len(l) call in the mkvec type
    assert mkvec(int, nil(int)) == []
    assert vunpack(int, 3, mkvec(int, mklist(int, [1,2,3]))) == [1,2,3]
    assert vcons(bool, 0, True, mkvec(bool, nil(bool))) == [True]
    assert head(bool, mkvec(bool, mklist(bool, [False]))) == False
    try:
        head(bool, mkvec(bool, nil(bool))) # type error
        # Error in head @ head(bool, mkvec(bool, nil(bool))) :
        # Expected Type(<function vec at 0x7f9800b7bb50>, <class
        # 'bool'>, 1), found Type(<function vec at 0x7f9800b7bb50>,
        # <class 'bool'>, 0)
        assert False
    except IndexError:
        pass
