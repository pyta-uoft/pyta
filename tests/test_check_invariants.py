"""
Test suite for checking the functionality of check_invariants.
"""

import pytest

from python_ta.contracts import PyTAContractError, check_invariants


class Person:
    """A custom data type that represents data for a person.

    Representation Invariants:
        - self.age >= 0
    """

    given_name: str
    age: int

    def __init__(self, given_name: str, age: int) -> None:
        """Initialize a new Person object."""
        self.given_name = given_name
        self.age = age


def test_no_errors() -> None:
    """Checks that check_invariants does not raise an error when representation invariants are satisfied."""
    person_obj = Person("Jim", 50)

    try:
        check_invariants(person_obj)
    except Exception:
        assert False


def test_raise_error() -> None:
    """Checks that check_invariants raises an error when representation invariants are violated."""
    person_obj = Person("Jim", -50)

    with pytest.raises(PyTAContractError):
        check_invariants(person_obj)
