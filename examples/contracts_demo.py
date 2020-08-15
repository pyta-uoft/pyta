"""python_ta contracts examples

The format for specifying preconditions are either:

1) Precondition: <python expr>
2) Preconditions:
     - <python expr>
     - <python expr>
     ...

Right now all <python expr> expressions must be written on a single line.
The same format is used with "Representation Invariant" instead of "Precondition".
The parsing is pretty strict right now, so these are case sensitive.
"""
from typing import List

def my_sum(numbers: List[int]) -> int:
    """Return the sum of the list of numbers.

    Preconditions:
      - len(numbers) > 0
      - numbers[0] == 100
      - numbers is special (this precondition is ignored)
    """
    return sum(numbers)


def my_sum2(numbers: List[int]) -> str:
    """Return the sum of the list of numbers.

    Preconditions:
      - len(numbers) > 0
      - numbers[0] == 100
    """
    return sum(numbers)


def my_sum3(numbers: List[int]) -> int:
    """Return the sum of the list of numbers.

    Preconditions:
      - len(numbers) > 0
      - numbers[0] == 100
      - numbers is special (this precondition is ignored)

    >>> my_sum3([])
    0
    """
    return sum(numbers)


def is_valid_name(name):
    return name.isalpha()


class Person:
    """A class representing a person.

    Representation Invariants:
      - self.age > 0
      - len(self.name) > 0
      - is_valid_name(self.name)
    """
    age: int
    name: str

    def __init__(self, name: str, age: int) -> None:
        """Initialize a new person.

        Preconditions:
            - age > 0
            - len(name) > 0
            - is_valid_name(name)
        """
        self.name = name
        self.age = age

    def decrease_age(self) -> None:
        self.age -= 100

    def decrease_and_increase_age(self, age_diff: int):
        """Illustrates limit of RI checking: does not check attribute setting in instance method."""
        self.age -= age_diff
        self.age += age_diff


class Student(Person):
    """A class representing a student.

    Representation Invariants:
      - len(self.id) == 8
    """
    id: str

    def __init__(self, name: str, age: int, id: str) -> None:
        """Initialize a new person.

        Preconditions:
            - age > 0
            - len(name) > 0
            - is_valid_name(name)
            - len(id) == 8
        """
        self.name = name
        self.age = age
        self.id = id


if __name__ == '__main__':
    # "Magic function" to activate all contracts and representation invariants in the given file.
    # Can also import decorators "check_contracts" for functions and "add_class_invariants" for classes.
    import python_ta.contracts as contracts
    contracts.check_all_contracts()

    # This call works properly.
    # my_sum([100, 200, 300])

    # This call will raise an error: the type contract is violated by the parameter.
    # my_sum('hello')

    # This call will raise an error: the first precondition is not satisfied.
    # my_sum([])

    # This call will raise an error: the second precondition is not satisfied.
    # my_sum([1, 2, 3])

    # This call will raise an error: the return type is violated.
    # my_sum2([100, 200, 300])

    # This doctest fails: the doctest in my_sum3 violates a precondition.
    # import doctest; doctest.testmod()

    # This object creation works properly.
    # p = Person('David', 100)

    # This object creation will raise an error: __init__ precondition is not satisfied.
    # Person('123', 20)

    # This attribute mutation will raise an error: representation invariant is violated.
    # p.age = -10

    # This method call will raise an error: representation invariant is violated at the end of the call.
    # p.decrease_age()

    # This method call works properly (the RI is not checked during the method body).
    # p.decrease_and_increase_age(100)

    # This object creation works properly.
    s = Student('Ibrahim', 200, '12345678')

    # This attribute mutation will raise an error: representation invariant from the Person superclass is violated.
    # s.age = -10
