import typing
import sys
from typing import *
from typing import CallableMeta
import astroid


class Monad():
    def __init__(self, value):
        self.value = value

    def getValue(self):
        return self.value

    def fmap(self, function):
        raise NotImplementedError

    def bind(self, function):
        raise NotImplementedError

    def __rmul__(self, function):
        return self.fmap(function)

    def __rshift__(self, function):
        if callable(function):
            result = self.bind(function)
            if not isinstance(result, Monad):
                raise TypeError("Operator '>>' must return a Monad instance.")
            return result
        else:
            if not isinstance(function, Monad):
                raise TypeError("Operator '>>' must return a Monad instance.")
            return self.bind(lambda _: function)


class TypeResult(Monad):
    """
    Represents the result of a type check operation that either succeeded or
    failed.
    """
    def __init__(self, value):
        raise NotImplementedError


class TypeInfo(TypeResult):
    """
    Represents the result of a successful type check operation
    Contains information about the inferred type of a node
    """

    def __init__(self, type_: type):
        if not isinstance(type_, type):
            raise TypeError
        super(TypeResult, self).__init__(type_)

    def __eq__(self, other):
        super(TypeResult, self).__eq__(other)
        if not isinstance(other, TypeResult):
            return False
        elif (self.getValue() == other.getValue()):
            return True
        else:
            return False

    def __str__(self):
        return f'TypeInfo: {self.value}'

    def fmap(self, function):
        """
        f:: (type -> type)
        function must take type and return type
        """
        return TypeInfo(function(self.value))

    def bind(self, function):
        """
        f :: (type -> TypeResult)
        function must take type, and return TypeResult
        """
        return function(self.getValue())


class TypeFail(TypeResult):
    """
    Represents the result of a failed type check operation
    Contains error message
    """
    def __init__(self, msg: str):
        if not isinstance(msg, str):
            raise TypeError
        super(TypeResult, self).__init__(msg)

    def __str__(self):
        return f'TypeFail: {self.value}'

    def __eq__(self, other):
        super(TypeFail, self).__eq__(other)
        if not isinstance(other, TypeFail):
            return False
        elif (self.getValue() == other.getValue()):
            return True
        else:
            return False

    def fmap(self, _):
        return self

    def bind(self, _):
        return self


def _gorg(x):
    if sys.version_info < (3, 6, 3):
        return typing._gorg(x)
    else:
        return x._gorg


def unify(t1: TypeResult, t2: TypeResult):
    """
    unify :: TypeResult -> TypeResult -> TypeResult
    """
    # Cases of TypeFail
    # If both TypeResults are TypeFails, will simply return first one
    if isinstance(t1, TypeFail):
        return t1 >> (lambda x: TypeFail(x))
    elif isinstance(t2, TypeFail):
        return t2 >> (lambda x: TypeFail(x))

    # Case of two generics
    # TODO: Change this to use binds instead of always looking up values
    # Currenly only accounts for lists
    elif isinstance(t1.getValue(), GenericMeta) and isinstance(
            t2.getValue(), GenericMeta):
        # Bind GenericMeta object from each TypeInfo to x and y,
        # pass to unify_generic
        return t1 >> (lambda x: t2 >> (lambda y: unify_generic(x, y)))

    # Case of generic and non-generic
    elif isinstance(t1.getValue(), GenericMeta) or isinstance(
            t2.getValue(), GenericMeta):
        return TypeFail("Cannot unify generic with primitive")

    # Case of unifying two concrete types
    elif t1.getValue() == t2.getValue():
        return t1

    # Types are incompatible
    else:
        return TypeFail(
            f'Incompatible Types {t1.getValue()} and {t2.getValue()}')


def unify_generic(t1: GenericMeta, t2: GenericMeta):
    """
    unify_generic :: GenericMeta -> GenericMeta -> TypeResult
    """
    # TODO: Change to properly extract values and check generic type
    g1, g2 = _gorg(t1), _gorg(t2)
    # Check that t1, t2 are of the same type
    if g1 == g2:
        # Check that t1, t2 are of the same length
        if len(t1.__args__) == len(t2.__args__):
            result_list = []
            for i, j in zip(t1.__args__, t2.__args__):
                # As __args__ is a list of types, these are wrapped as
                # TypeInfo objects before being passed to unify
                unify_result = unify(TypeInfo(i), TypeInfo(j))
                if not isinstance(unify_result, TypeFail):
                    # If unify result is a success, type is extracted and
                    # stored in result_list
                    # TODO: Use binding instead?
                    result_list.append(unify_result.getValue())
                else:
                    # If, at any point, a TypeFail occurs, the function simply
                    # returns that TypeFail instance
                    return unify_result
            if g1 == List:
                return TypeInfo(List[result_list[0]])
            elif g1 == Tuple:
                return TypeInfo(Tuple[tuple(result_list)])
            elif g1 == Callable:
                return TypeInfo(g1[result_list[:-1], result_list[-1]])
            # Reaches this case when generic is not List, Tuple or Callable
            else:
                return TypeFail("Generic not yet supported")
        else:
            return TypeFail("Generics must be of same size")
    else:
        return TypeFail("Generic types do not match")


if __name__ == '__main__':
    a = TypeInfo(bool)
    b = TypeFail("Type missing")
    c = TypeInfo(str)
    print("Primitives: ")
    print(f'Unifying {a} and {a}: \n\t{unify(a, a)}\n')
    print(f'Unifying {a} and {b}: \n\t{unify(a, b)}\n')
    print(f'Unifying {a} and {c}: \n\t{unify(a, c)}\n')

    print("\nLists: ")
    e = TypeInfo(type([True, False, False]))
    f = TypeInfo(List[bool])
    g = TypeInfo(List[str])
    h = TypeInfo(List[str])
    q = TypeInfo(List[List[int]])
    r = TypeInfo(List[List[int]])
    print(f'Unifying {e} and {f}: \n\t{unify(e, f)}\n')
    print(f'Unifying {f} and {g}: \n\t{unify(f, g)}\n')
    print(f'Unifying {g} and {h}: \n\t{unify(g, h)}\n')
    print(f'Unifying {q} and {r}: \n\t{unify(q, r)}\n')

    print("\nTuples: ")
    i = TypeInfo(Tuple[int, int])
    j = TypeInfo(Tuple[int, int])
    k = TypeInfo(Tuple[int, str])
    l = TypeInfo(Tuple[int, int, int])
    m = TypeInfo(Tuple[int, int, int])
    n = TypeInfo(Tuple[int, int, str])
    o = TypeInfo(Tuple[Tuple[Tuple[int, str], Tuple[bool, int]], float])
    p = TypeInfo(Tuple[Tuple[Tuple[int, str], Tuple[bool, int]], float])
    print(f'Unifying {i} and {j}: \n\t{unify(i, j)}\n')
    print(f'Unifying {j} and {k}: \n\t{unify(j, k)}\n')
    print(f'Unifying {l} and {m}: \n\t{unify(l, m)}\n')
    print(f'Unifying {j} and {l}: \n\t{unify(j, l)}\n')
    print(f'Unifying {m} and {n}: \n\t{unify(m, n)}\n')
    print(f'Unifying {o} and {p}: \n\t{unify(o, p)}\n')

    print("\nCallables: ")
    s = TypeInfo(Callable[[int, bool], float])
    t = TypeInfo(Callable[[int, bool], float])
    print(f'Unifying {s} and {t}: \n\t{unify(s, t)}\n')
