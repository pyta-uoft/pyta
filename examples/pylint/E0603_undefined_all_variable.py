"""pylint: Undefined variable %r in __all__ Used when an undefined variable is referenced in __all__.

"""

""" mod1.py """

__all__ = ['a', 'b']

a = 1
b = None

""" mod2.py """

from mod1 import *

print(mod1.a)
print(mod1.b) # Error on this line
