import pytest
from python_ta.contracts import check_contracts


@check_contracts
class Person:
    """
    Represent a person.

    Representation Invariants: 
    - self.age > 0
    - len(self.name) > 0
    """

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


p1 = Person("David", 31)


def change_age(person, new_age):
    person.age = new_age


def test_change_age_invalid_over() -> None:
    """
    Change the age to larger than 100. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        p1.change_age(200)
    msg = str(excinfo.value)
    assert 'age < 150' in msg


def test_change_name_valid() -> None:
    """
    Change the name using a valid name.
    """
    p1.name = "Ignas"
    assert p1.name == "Ignas"


def test_change_name_invalid() -> None:
    """
    Change the name using a valid name.
    """
    with pytest.raises(AssertionError) as excinfo:
        p1.change_name("")
    msg = str(excinfo.value)
    assert 'len(self.name) > 0' in msg


def test_change_age_invalid_under() -> None:
    """
    Change the age to a negative number. Expect an exception.
    """
    with pytest.raises(AssertionError) as excinfo:
        p1.change_name("David")  # Changing it back to a valid value.
        p1.age = -10
    msg = str(excinfo.value)
    assert 'self.age > 0' in msg


def test_change_age_invalid_in_method() -> None:
    """
    Call a method that changes age to something invalid but back to something valid.
    Expects normal behavior.
    """
    age = p1.decrease_and_increase_age(10)
    assert age == 10


def test_same_method_names() -> None:
    """
    Call a method with the same name as an instance method and ensure reprsentation invariants are checked.
    Expects normal behavior.
    """

    with pytest.raises(AssertionError) as excinfo:
        change_age(p1, -10)
    msg = str(excinfo.value)
    assert 'self.age > 0' in msg
