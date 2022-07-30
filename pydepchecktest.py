# type: ignore
from pydepcheck import type_, Type

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
    try:
        add(1, "bar")
        add(1, add(2, 3))
        add(1, id(str, "foo"))
    except:
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
    get_from_a_box(put_into_a_box(int, 1))

if __name__ == '__main__':
    test_id()
    test_box()
    test_add()


