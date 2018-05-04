import typing
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


def unify(t1: TypeResult, t2: TypeResult):
    """
    unify :: TypeResult -> TypeResult -> TypeResult
    """
    # Cases of TypeFail
    # If both TypeResults are TypeFails, will simply return first one
    if isinstance(t1, TypeFail):
        return TypeFail(t1.getValue())
    elif isinstance(t2, TypeFail):
        return TypeFail(t2.getValue())

    # Case of two generics
    # TODO: Change this to use binds instead of always looking up values
    # Currenly only accounts for lists
    elif isinstance(t1.getValue(), GenericMeta) and isinstance(
            t2.getValue(), GenericMeta):
        print("Generic! Checking...")
        return unify_generic(t1.getValue(), t2.getValue())

    # Case of generic and non-generic
    elif isinstance(t1.getValue(), GenericMeta) or isinstance(
            t2.getValue(), GenericMeta):
        return TypeFail("Cannot unify generic with primitive")

    # Case of unifying two concrete types
    elif t1.getValue() == t2.getValue():
        return t1

    # Types are incompatible
    else:
        return TypeFail("Incompatible Types")


def unify_generic(t1: GenericMeta, t2: GenericMeta):
    """
    unify_generic :: GenericMeta -> GenericMeta -> TypeResult
    """
    # TODO: Change to properly extract values and check generic type
    return unify(TypeInfo(t1.__args__[0]), TypeInfo(t2.__args__[0]))


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
    print(f'Unifying {e} and {f}: \n\t{unify(e, f)}\n')
    print(f'Unifying {f} and {g}: \n\t{unify(f, g)}\n')
    print(f'Unifying {g} and {h}: \n\t{unify(g, h)}\n')

    print("\nTuples: ")
    i = TypeInfo(Tuple[int, int])
    j = TypeInfo(Tuple[int, int])
    print(f'Unifying {i} and {j}: \n\t{unify(i, j)}\n')
