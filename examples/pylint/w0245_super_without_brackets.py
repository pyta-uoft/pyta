class Animal:
    """An animal"""

    def __init__(self) -> None:
        print('parent class')


class Cat(Animal):
    """A cat"""

    def __init__(self) -> None:
        super  # Error on this line, no brackets following super call
        print('This is a cat')
