class Animal:
    """Abstract class to be implemented by all animals."""
    _name: str

    def __init__(self, name: str) -> None:
        self._name = name

    def make_sound(self, mood: str) -> None:
        """Print a sound that the animal would make in a given mood."""
        raise NotImplementedError


class Dog(Animal):
    """A man's best friend."""

    def make_sound(self, state: str) -> None:  # Error: Parameter differs
        if state == 'happy':
            print("Woof Woof!")
        elif state == 'angry':
            print("Grrrrrrr!!")
