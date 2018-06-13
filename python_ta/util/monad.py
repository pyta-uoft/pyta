from typing import *
from inspect import signature


class Monad():

    def __init__(self):
        raise NotImplementedError

    def bind(self, fn : Callable[[TypeVar('T')], 'Monad']) -> 'Monad':
        raise NotImplementedError

    def __rshift__(self, fn : Callable[[TypeVar('T')], 'Monad']) -> 'Monad':
        return self.bind(fn)

    def getValue(self): # TODO: underscore naming
        return self.value


class Failable(Monad):

    def __init__(self, value):
        self.value = value

    def __eq__(self, other):
        return self.__class__ == other.__class__ and self.value == other.value

    def __str__(self):
        return self.value.__str__()

    def bind(self, fn):
        try:
            sig = signature(fn)
            min_args = 0
            for p in sig.parameters.values():
                if p.default is p.empty:
                    min_args += 1
            num_def_args = len(sig.parameters) - min_args

            if min_args == 1:
                # Return a value
                return fn(self.value)
            else:
                # Return a function that takes in at least one argument
                return self.curry(fn, [self.value], 1, min_args, num_def_args)
        except ValueError:
            return fn(self.value)

    def curry(self, fn, args, num_args, min_args, num_def_args):
        if num_args > min_args:
            return fn(*args)
        elif num_args == min_args and num_def_args == 0:
            return fn(*args)
        else:
            return lambda *x: self.curry(fn, (args + list(x)), num_args + len(x), min_args, num_def_args)


def failable_map(fn : Callable[[TypeVar('T')], Failable], lst : List[Failable]):
    # TODO: allow arbitrary containers like tuples
    if lst == []:
        return Failable([])
    return lst[0] >> (lambda fst: (failable_map(fn, lst[1:]) >> (lambda rest: Failable([fst] + rest))))


def failable_collect(lst : List[Failable]):
    return failable_map(lambda x: x, lst)