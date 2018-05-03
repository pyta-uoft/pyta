import typing
import astroid


class Monad():
    def __init__(self, value):
        self.value = value

    def getValue(self):
        return self.value

    def fmap(self, function):
        raise NotImplementedError

    def amap(self, functorValue):
        raise NotImplementedError

    def bind(self, function):
        raise NotImplementedError

    def __rmul__(self, function):
        return self.fmap(function)

    def __and__(self, functorValue):
        return self.amap(functorValue)

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
        """

        """
        if not isinstance(type_, type):
            raise TypeError
        super(TypeResult, self).__init__(type_)

    def fmap(self, function):
        return TypeInfo(function(value))

    def __str__(self):
        return f'Inferred Type: {self.value}'


class TypeFail(TypeResult):
    """
    Represents the result of a failed type check operation
    Contains error message
    """
    def __init__(self, msg: str):
        """

        """
        super(TypeResult, self).__init__(msg)

    def __str__(self):
        return f'Error: {self.value}'


if __name__ == '__main__':
    a = TypeInfo(bool)
    print(a)
    b = TypeFail("Error Message")
    print(b)
    c = TypeInfo(str)
    print(c)
