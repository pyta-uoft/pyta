"""Example for E9982 invalid representation invariant syntax checker"""


class Person:
    """A class representing a person.

    Representation Invariants:
       - self.age !== 0  # error on this line
       - self.age >= 0  # no error on this line
    """

    age: int

    def __init__(self, age: int) -> None:
        self.age = age
