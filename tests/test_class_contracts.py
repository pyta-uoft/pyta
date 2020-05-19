import pytest
import math
from python_ta.contracts import check_all_contracts


def is_valid_name(name):
    return name.isalpha()


class Person:
    """
    Represent a person.

    Representation Invariants: 
    - self.age > 0
    - len(self.name) > 0
    - is_valid_name(self.name)
    """

    age: int
    name: str

    def __init__(self, name, age):
        self.name = name
        self.age = age

    def change_name(self, name: str) -> str:
        self.name = name
        return name

    def change_age(self, age: int) -> int:
        """
        Precondition: age < 150
        """
        self.age = age
        return age

    def decrease_and_increase_age(self, age: int) -> int:
        self.age = -10
        self.age = age
        return age


def change_age(person, new_age):
    person.age = new_age


class Pizza:
    """
    Representation Invariants:
    - len(self.ingredients) > 0
    - 0 < self.radius <= 10
    """

    def __init__(self, radius, ingredients):
        self.radius = radius
        self.ingredients = ingredients

    @classmethod
    def margherita(cls, radius):
        return cls(radius, ['mozzarella', 'tomatoes'])

    def area(self):
        return self.circle_area(self.radius)

    @staticmethod
    def circle_area(r):
        """
        Precondition: r > 0
        """
        return r ** 2 * math.pi


# Decorating everything in this file
check_all_contracts(__name__)


@pytest.fixture
def person():
    return Person("David", 31)


def test_change_age_invalid_over(person) -> None:
    """
    Change the age to larger than 100. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        person.change_age(200)
    msg = str(excinfo.value)
    assert 'age < 150' in msg


def test_change_name_valid(person) -> None:
    """
    Change the name using a valid name.
    """
    person.name = "Ignas"
    assert person.name == "Ignas"


def test_change_name_invalid_nonalpha(person) -> None:
    """
    Change name to contain non-alphabet characters. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        person.name = "$$"
    msg = str(excinfo.value)
    assert 'is_valid_name(self.name)' in msg


def test_change_age_invalid_in_method(person) -> None:
    """
    Call a method that changes age to something invalid but back to something valid.
    Expects normal behavior.
    """
    age = person.decrease_and_increase_age(10)
    assert age == 10


def test_same_method_names(person) -> None:
    """
    Call a method with the same name as an instance method and ensure reprsentation invariants are checked.
    Expects normal behavior.
    """

    with pytest.raises(AssertionError) as excinfo:
        change_age(person, -10)
    msg = str(excinfo.value)
    assert 'self.age > 0' in msg

def test_wrong_name_type(person) -> None:
    """Change name to an int. Expect an exception."""

    with pytest.raises(AssertionError):
        person.name = 5


def test_create_margherita_invalid() -> None:
    """
    Calculate circle area with invalid r. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        Pizza.margherita(0)
    msg = str(excinfo.value)
    assert '0 < self.radius <= 10' in msg


def test_circle_area_valid() -> None:
    """
    Calculate circle area with valid r.
    """
    a = Pizza.circle_area(10)
    assert a == (10 ** 2 * math.pi)


def test_circle_area_invalid() -> None:
    """
    Calculate circle area with invalid r. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        Pizza.circle_area(0)
    msg = str(excinfo.value)
    assert 'r > 0' in msg
