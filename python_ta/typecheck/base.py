from typing import *
from typing import GenericMeta, TupleMeta, _gorg


Num = TypeVar('number', int, float)
a = TypeVar('a')
MulNum = TypeVar('mul_n', int, float, str, List[a])
tup1 = TypeVar('tup1')
tup2 = TypeVar('tup2')

class TuplePlus(TypeVar, _root=True):
    pass


class TupleSubscript(TypeVar, _root=True):
    pass


TYPE_SIGNATURES = {
    int: {
        '__add__': Callable[[int, Num], Num],
        '__sub__': Callable[[int, Num], Num],
        '__mul__': Callable[[int, MulNum], MulNum],
        '__idiv__': Callable[[int, Num], Num],
        '__mod__': Callable[[int, Num], Num],
        '__pow__': Callable[[int, Num], Num],
        '__div__': Callable[[int, Num], float],
    },
    float: {
        '__add__': Callable[[float, Num], float],
        '__sub__': Callable[[float, Num], float],
        '__mul__': Callable[[float, Num], float],
        '__idiv__': Callable[[float, Num], float],
        '__mod__': Callable[[float, Num], float],
        '__pow__': Callable[[float, Num], float],
        '__div__': Callable[[float, Num], float],
    },
    str: {
        '__add__': Callable[[str, str], str],
        '__mul__': Callable[[str, int], str]
    },
    List: {
        '__add__': Callable[[List[a], List[a]], List[a]],
        '__mul__': Callable[[List[a], int], List[a]],
        '__getitem__': Callable[[List[a], int], a]
    },
    Tuple: {
        '__add__': Callable[[Tuple[tup1], Tuple[tup2]], TuplePlus('tup+', tup1, tup2)],
    }
}


def op_to_dunder(op):
    """Return the dunder method name corresponding to op."""
    if op == '+':
        return '__add__'
    elif op == '-':
        return '__sub__'
    elif op == '*':
        return '__mul__'
    elif op == '//':
        return '__idiv__'
    elif op == '%':
        return '__mod__'
    elif op == '/':
        return '__div__'
    elif op == '**':
        return '__pow__'
    else:
        return ''


def lookup_method(caller_type, name):
    """Lookup method with the given name for the given type."""
    if isinstance(caller_type, TupleMeta):
        caller_origin = Tuple
    elif isinstance(caller_type, GenericMeta):
        caller_origin = _gorg(caller_type)
    else:
        caller_origin = caller_type

    return TYPE_SIGNATURES[caller_origin][name]


def fresh_tvar():
    """Return a fresh type variable."""
    fresh_tvar._count += 1
    return TypeVar('_T' + str(fresh_tvar._count))


fresh_tvar._count = 0
