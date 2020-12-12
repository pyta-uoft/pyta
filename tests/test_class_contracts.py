from dataclasses import dataclass
import pytest
import math
from python_ta.contracts import check_all_contracts
from typing import List, Set


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
    fav_foods: List[str]

    def __init__(self, name, age, fav_food):
        self.name = name
        self.age = age
        self.fav_foods = fav_food

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
    
    def add_fav_food(self, food):
        self.fav_foods.append(food)


def change_age(person, new_age):
    person.age = new_age


class Pizza:
    """
    Representation Invariants:
    - len(self.ingredients) > 0
    - 0 \
        < self.radius \
            <= 10
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


@dataclass
class SetWrapper:
    """A wrapper around a set.

    Representation Invariants:
        - all(x in self.set for x in {1, 2, 3})
    """
    set: Set[int]


@pytest.fixture
def person():
    return Person("David", 31, ["Sushi"])


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

def test_wrong_food_type(person) -> None:
    """Change fav food to an int. Expect an exception."""

    with pytest.raises(AssertionError):
        person.fav_foods = 5

def test_wrong_food_type_instance_method(person) -> None:
    """Violates type annotation within an instance method. Expect exception."""

    with pytest.raises(AssertionError):
        person.add_fav_food(5)


def test_create_margherita_invalid() -> None:
    """
    Create circle area with invalid r. Also tests multiline conditions.
    Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        Pizza.margherita(0)
    msg = str(excinfo.value)
    assert '0 \
        < self.radius \
            <= 10' in msg


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


def test_set_wrapper_valid() -> None:
    """
    Test the SetWrapper representation invariant on a valid instance.
    """
    my_set = SetWrapper(set={1, 2, 3})
    assert my_set.set == {1, 2, 3}


def test_set_wrapper_invalid() -> None:
    """
    Test the SetWrapper representation invariant on a valid instance.
    """
    with pytest.raises(AssertionError) as excinfo:
        SetWrapper(set={1, 2, -3})
    msg = str(excinfo.value)
    assert 'all(x in self.set for x in {1, 2, 3})' in msg


class NoInit:
    """A class with no initializer.

    Representation Invariants:
        - abs(1) < 0  # This is always False
    """
    def method(self) -> int:
        """Method to test that representation invariant is checked on method calls."""
        return 1


def test_no_init_setattr() -> None:
    """
    Check that a built-in function (abs) can be called successfully
    from a representation invariant of a class with no __init__ method, when setting an attribute.
    """
    with pytest.raises(AssertionError) as excinfo:
        n = NoInit()
        n.attr = 1

    msg = str(excinfo.value)
    assert 'abs(1) < 0' in msg


def test_no_init_method() -> None:
    """
    Check that a built-in function (abs) can be called successfully
    from a representation invariant of a class with no __init__ method, when calling a method.
    """
    with pytest.raises(AssertionError) as excinfo:
        n = NoInit()
        n.method()

    msg = str(excinfo.value)
    assert 'abs(1) < 0' in msg


class NoInit2:
    """A class with no initializer.

    Representation Invariants:
        - is_valid_name('123')  # This is always False
    """

    def method(self) -> int:
        """Method to test that representation invariant is checked on method calls."""
        return 1


def test_no_init_setattr2() -> None:
    """
    Check that a user-defined function (is_valid_name) can be called successfully
    from a representation invariant of a class with no __init__ method, when setting an attribute.
    """
    with pytest.raises(AssertionError) as excinfo:
        n = NoInit2()
        n.attr = 1

    msg = str(excinfo.value)
    assert "is_valid_name('123')" in msg


def test_no_init_method2() -> None:
    """
    Check that a user-defined function (is_valid_name) can be called successfully
    from a representation invariant of a class with no __init__ method, when calling a method.
    """
    with pytest.raises(AssertionError) as excinfo:
        n = NoInit2()
        n.method()

    msg = str(excinfo.value)
    assert "is_valid_name('123')" in msg


def setup_module() -> None:
    """Pytest hook for setting up the module"""
    check_all_contracts(__name__, decorate_main=False)


if __name__ == '__main__':
    pytest.main(['test_class_contracts.py'])
