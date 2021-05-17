"""Example for E9970 missing-param-type"""
def add_one(n) -> int:
    """Return n + 1."""
    return n + 1


class ExampleClass:
    """Class docstring."""
    inst_attr: int

    def __init__(self) -> None:
        """Initialize an instance of this class."""
        self.inst_attr = 0

    def inst_method(self, x) -> int:  # Missing function parameter type annotation
        """Function docstring."""
        return self.inst_attr + x

    @staticmethod
    def static_function(x) -> int:  # Missing function parameter type annotation
        """Static function docstring."""
        return x

    @classmethod
    def class_method(cls, x) -> int:  # Missing function parameter type annotation
        """Class function docstring."""
        return x
