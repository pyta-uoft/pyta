class Animal:
    """Abstract class to be implemented by all animals."""

    def __init__(self, name) -> None:
        self.name = name

    def make_sound(self) -> str:
        raise NotImplementedError


class Cat(Animal):  # Error: Method 'make_sound' is not overridden
    """A worthy companion."""
    pass
