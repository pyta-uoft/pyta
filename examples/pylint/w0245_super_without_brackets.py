class Animal:
    """A class that represents an animal"""
    def __init__(self) -> None:
        print('This is an animal')


class Cat(Animal):
    """A class that represents a cat"""
    def __init__(self) -> None:
        super.__init__() # Error on this line, no brackets following super call
        print('This is a cat')
