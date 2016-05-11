"""pylint: not context manager
"""


def contextmanagerdecorator(cls):
    class DecoClass(cls):
        def __enter__(self):
            """
            __enter__
            """
            pass  # Error on this line

        def __exit__(self, *n, **kw):
            """
            __exit__
            """
            pass  # Error on this line
    return DecoClass

@contextmanagerdecorator
class RegularClass(object):
    pass

obj = RegularClass()
with obj:
    pass
