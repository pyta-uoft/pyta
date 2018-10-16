import sys
import typing
from typing import ForwardRef, _GenericAlias


def _get_name(t: type) -> str:
    """If t is associated with a class, return the name of the class; otherwise, return a string repr. of t"""
    if isinstance(t, ForwardRef):
        return t.__forward_arg__
    elif isinstance(t, type):
        return t.__name__
    elif isinstance(t, _GenericAlias):
        return '{} of {}'.format(_get_name(t.__origin__),
                                 ', '.join(_get_name(arg) for arg in t.__args__))
    else:
        return str(t)


def _gorg(x):
    """Make _gorg compatible for Python 3.6.2 and 3.6.3."""
    if sys.version_info >= (3, 7, 0):
        return x.__origin__
    if sys.version_info < (3, 6, 3):
        return typing._gorg(x)
    else:
        return x._gorg
