"""Module docstring."""


def example_function(x):
    """Function docstring."""
    return x


class ExampleClass:
    """Class docstring."""
    class_var = 0

    def __init__(self):
        """Function docstring."""
        self.inst_attr = "Hello"

    def inst_method(self, x):
        """Function dosctring."""
        return self.inst_attr

    @staticmethod
    def static_function(x):
        """Static function docstring."""
        return x

    @classmethod
    def class_method(cls, x):
        """Class function docstring."""
        return x
