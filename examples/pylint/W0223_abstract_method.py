class Animal:

    def __init__(self, name) -> None:
        self.name = name

    def make_sound(self) -> str:
        raise NotImplementedError


class Cat(Animal):  # Error on this line
    pass
