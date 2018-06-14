from typing import *


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
        return fn(self.value)

        
def failable_map(fn: Callable[[TypeVar('T')], Failable], itr: Iterable[Failable]) -> Failable:
    lst = list(itr)
    if lst == []:
        return Failable([])
    return fn(lst[0]) >> (lambda fst: (failable_map(fn, lst[1:]) >> (lambda rest: Failable([fst] + rest))))
    
    
def failable_collect(itr: Iterable[Failable]) -> Failable:
    return failable_map(lambda x: x, itr)
