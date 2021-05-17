"""Example for E9972 missing-attribute-type"""


class ExampleClass:
    """Class docstring."""
    def __init__(self):  # Missing return type annotation
        """Initialize a new instance of this class."""
        self.inst_attr: str = 'hi'  # Instance variable should be annotated in class body
        self.inst_attr2 = True  # Instance variable should be annotated in class body


class A:
    """Class docstring."""
    x: int


class B(A):
    """Class B is a subclass of A."""

    def method(self):
        """Function docstring"""
        self.x = 15  # No error because attribute has type annotation in the parent class
