"""Example for E9971 missing-return-type"""
def add_one(n: int):
    """Return n + 1."""
    return n + 1


class ExampleClass:
    """Class docstring."""
    inst_attr: int

    def __init__(self):
        """Initialize an instance of this class."""
        self.inst_attr = 0

    def inst_method(self, x: int):  # Missing return type annotation
        """Function docstring."""
        return self.inst_attr + x

    @staticmethod
    def static_function(x: int):  # Missing return type annotation
        """Static function docstring."""
        return x

    @classmethod
    def class_method(cls, x: str):  # Missing return type annotation
        """Class function docstring."""
        return x
