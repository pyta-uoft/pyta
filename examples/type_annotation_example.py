"""Module docstring."""


def example_function(x):  # Missing function parameter and return type annotation
    """Function docstring."""
    return x


class ExampleClass:
    """Class docstring."""
    class_var = 0  # Missing variable type annotation
    inst_attr = "Hello"  # Missing variable type annotation

    def __init__(self):  # Missing return type annotation
        """Function docstring."""
        self.inst_attr: str  # Instance variable should be annotated in class body
        self.inst_attr_2 = True  # Instance variable should be annotated in class body

    def inst_method(self):  # Missing return type annotation
        """Function docstring."""
        return self.inst_attr

    @staticmethod
    def static_function(x):  # Missing function parameter and return type annotation
        """Static function docstring."""
        return x

    @classmethod
    def class_method(cls, x):  # Missing function parameter and return type annotation
        """Class function docstring."""
        return x


class A:
    """Class docstring."""
    x: int


class B(A):
    """Class B is a subclass of A."""
    def method(self):
        """Function docstring"""
        self.x = 15  # Doesn't complain about missing type annotation because it's in the parent class
