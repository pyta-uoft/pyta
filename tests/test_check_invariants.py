"""
Test suite for checking the functionality of check_invariants.
"""

from typing import List

import pytest

from python_ta.contracts import check_contracts, check_invariants


@check_contracts
class Person:
    """A custom data type that represents data for a person.

    Representation Invariants:
        - self.age >= 0
        - len(self.friends) > 1
    """

    given_name: str
    age: int
    friends: List[str]

    def __init__(self, given_name: str, age: int, friends: List[str]) -> None:
        """Initialize a new Person object."""
        self.given_name = given_name
        self.age = age
        self.friends = friends


def test_no_errors() -> None:
    """Checks that check_invariants does not raise an error when representation invariants are satisfied."""
    person = Person("Jim", 50, ["Pam", "Dwight"])

    try:
        check_invariants(person)
    except Exception:
        pytest.fail("check_invariants has incorrectly raised an error")


def test_raise_error() -> None:
    """Checks that check_invariants raises an error when representation invariants are violated."""
    person = Person("Jim", 50, ["Pam", "Dwight"])
    person.friends.pop()

    with pytest.raises(AssertionError):
        check_invariants(person)
