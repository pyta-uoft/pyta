"""pylint: too many ancestors

Maximum number of parents for a class (see R0901).

Used when class has too many parent classes, try to reduce this to get a simpler
(and so easier to use) class.

Default: 7
"""

class A:
    """Inherited me"""

class B:
    """Inherited me"""

class C:
    """Inherited me"""

class D:
    """Inherited me"""

class E:
    """Inherited me"""

class F:
    """Inherited me"""

class G:
    """Inherited me"""

class Inheritor(A, B, C, D, E, F, G):
    """Inherits 7 (parent) classes."""
