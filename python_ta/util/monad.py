from typing import *


class Monad():

	def __init__(self): # like return
		raise NotImplementedError
		
	def bind(self, fn : Callable[[TypeVar('T')], 'Monad']) -> 'Monad':
		raise NotImplementedError
		
	def __rshift__(self, fn : Callable[[TypeVar('T')], 'Monad']) -> 'Monad':
		return self.bind(fn)
	
				
class Failable(Monad):

	def __init__(self, value):
		self.value = value
		
	def __eq__(self, other):
		if not isinstance(other, Failable): return False
		return self.value == other.value
		
	def __str__(self):
		return self.value.__str__()
		
	def bind(self, fn):
		return fn(self.value)
		
		
class ErrorInfo(Monad):

	def __init__(self, msg):
		self.msg = msg
		
	def __eq__(self, other):
		if not isinstance(other, ErrorInfo): return False
		return self.msg == other.msg
		
	def __str__(self):
		return self.msg
		
	def bind(self, fn):
		return self
		
		
def failable_map(fn, lst): # TODO: allow arbitrary containers like tuples
	if lst == []:
		return Failable([])
	return lst[0] >> (lambda fst: (failable_map(fn, lst[1:]) >> (lambda rest: Failable([fst] + rest))))
	
def failable_collect(lst):
	return failable_map(lambda x: x, lst)
		

# TODO: this would replace the same class in typecheck/base.py
class TypeErrorInfo(ErrorInfo):

	def __init__(self, msg, node=None):
		self.msg = msg
		self.node = node
		
	def __eq__(self, other):
		if not isinstance(other, TypeError): return False
		return self.msg == other.msg and self.node == other.node
		
		
if __name__ == "__main__":
	lst1 = [Failable(int), Failable(bool)]
	print(failable_collect(lst1)) # should print '[<class 'int'>, <class 'bool'>]'
	lst2 = [Failable(int), TypeErrorInfo('Type error')]
	print(failable_collect(lst2)) # should print 'Type error'