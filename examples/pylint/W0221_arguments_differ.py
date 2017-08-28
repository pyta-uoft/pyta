class Animal:
    """Abstract class which should be implemented by all animals."""

    def __init__(self, name: str) -> None:
        self._name = name

    def make_sound(self, mood: str) -> None:
        """Print a sound that the animal would make in a given mood."""
        raise NotImplementedError


class Dog(Animal):
    """Class representing a dog."""

    def make_sound(self, state: str) -> None:  # Error on this line
        if state == 'happy':
            print("Woof Woof!")
        elif state == 'angry':
            print("Grrrrrrr!!")
