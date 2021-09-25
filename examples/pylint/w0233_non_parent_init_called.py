class ClassA:
    """An unrelated class."""

    def __init__(self) -> None:
        pass

class Parent:
    """A parent class."""

    def __init__(self) -> None:
        pass

class Child(Parent):
    """A child class."""

    def __init__(self) -> None:
        ClassA.__init__(self)  # `ClassA` is not a parent of `Child`
