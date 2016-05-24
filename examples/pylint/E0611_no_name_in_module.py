""" mod1.py """ # inside of mod1 module.

__all__ = ['a', 'b']

a = 1
b = 2 # There is no variable called c.

""" mod2.py """ # inside of mod1 module.

from mod1 import *

print(mod1.a)
print(mod1.b)
print(mod1.c) # But c is used here, which caused an error.
