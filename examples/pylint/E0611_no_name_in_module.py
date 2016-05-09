"""pylint: Name %r cannot be found in module %r.

"""

""" mod1.py """

__all__ = ['a', 'b']

a = 1
b = 2

""" mod2.py """

from mod1 import *

print(mod1.a)
print(mod1.b)
print(mod1.c) # Error on this line