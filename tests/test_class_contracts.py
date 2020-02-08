import pytest
from python_ta.contracts import check_contracts


@check_contracts
class Person():
    """
    Represent a person.

    Representation Invariants: 
    - self.age > 0
    - len(self.name) > 0
    """

    def __init__(self, name, age):
        self.name = name
        self.age = age

    @check_contracts
    def change_name(self, name: str) -> str:
        self.name = name
        return name

    @check_contracts
    def change_age(self, age: int) -> int:
        """
        Precondition: age < 150
        """
        self.age = age
        return age


p1 = Person("David", 31)


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
    p1.change_name("Ignas")
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
        p1.change_age(-10)
    msg = str(excinfo.value)
    assert 'self.age > 0' in msg