import sys
from typing import Dict, List, Set

import pytest

from python_ta.contracts import check_contracts


def test_nullary_return_int() -> None:
    """Calling a nullary function with the correct return type (int)."""

    @check_contracts
    def nullary() -> int:
        return 1

    nullary()


def test_nullary_return_dict() -> None:
    """Calling a nullary function with the correct return type (Dict)."""

    @check_contracts
    def nullary() -> Dict[str, int]:
        return {"one": 1}

    nullary()


def test_nullary_return_none() -> None:
    """Calling a nullary function with the correct return type (None)."""

    @check_contracts
    def nullary() -> None:
        3 + 4

    nullary()


def test_nullary_return_wrong_type() -> None:
    """Calling a nullary function with the incorrect return type."""

    @check_contracts
    def nullary() -> str:
        return 1

    with pytest.raises(AssertionError):
        nullary()


def test_nullary_return_dict_wrong() -> None:
    """Calling a nullary function with the incorrect return type (Dict)."""

    @check_contracts
    def nullary() -> Dict[str, int]:
        return {1: 1}

    with pytest.raises(AssertionError):
        nullary()


def test_nullary_no_return_type() -> None:
    """Calling a nullary function with no specified return type passes."""

    @check_contracts
    def nullary():
        return "string"

    nullary()


@check_contracts
def _my_sum(numbers: List[int]) -> int:
    return sum(numbers)


def test_my_sum_list_int_argument() -> None:
    """Calling _my_sum with a list of integers passes type check."""
    _my_sum([1, 2, 3])


def test_my_sum_empty_list_argument() -> None:
    """Calling _my_sum with an empty list passes type check."""
    _my_sum([])


def test_my_sum_list_mixed_argument() -> None:
    """Calling _my_sum with a list containing not just ints fails type check."""
    with pytest.raises(AssertionError):
        _my_sum([1, 2, "hello"])


@check_contracts
def _my_sum_one_precondition(numbers: List[int]) -> int:
    """Return the sum of a list of numbers.

    Precondition: len(numbers) > 2
    """
    return sum(numbers)


def test_my_sum_one_pre_valid() -> None:
    """Calling _my_sum_one_precondition on a valid input."""
    assert _my_sum_one_precondition([1, 2, 3]) == 6


def test_my_sum_one_wrong_type() -> None:
    """Calling _my_sum_one_precondition on a value of the wrong type."""
    with pytest.raises(AssertionError):
        _my_sum_one_precondition("hi")


def test_my_sum_one_pre_violation() -> None:
    """Calling _my_sum_one_precondition one a value of the right type,
    but that violates the docstring precondition.
    """
    with pytest.raises(AssertionError) as excinfo:
        _my_sum_one_precondition([1])

    msg = str(excinfo.value)
    assert "len(numbers) > 2" in msg


# Checking to see if functions we defined are in-scope for preconditions


def is_even(lst: List[int]) -> bool:
    return all([(not x & 1) for x in lst])


@check_contracts
def _is_even_sum(numbers: List[int]) -> int:
    """Return the sum of a list of numbers.

    Precondition: is_even(numbers)
    """
    return sum(numbers)


def test_is_even_sum_valid() -> None:
    """Calling _is_even_sum on a valid input."""
    assert _is_even_sum([2, 4, 6]) == 12


def test_is_even_sum_violation() -> None:
    """Calling _is_even_sum one a value of the right type,
    but that violates the docstring precondition.
    """
    with pytest.raises(AssertionError) as excinfo:
        _is_even_sum([1, 2])

    msg = str(excinfo.value)
    assert "is_even(numbers)" in msg


@check_contracts
def search(numbers: Set[int]) -> bool:
    """Search for a number in a set.

    Illustrates a preconditions with a double comprehension.

    Preconditions:
        - all({n + m > 0 for n in numbers for m in numbers})
    """
    return 1 in numbers


def test_search_valid() -> None:
    """Test search on a valid input."""
    assert search({1, 2})


def test_search_invalid() -> None:
    """Test search on an invalid input."""
    with pytest.raises(AssertionError) as excinfo:
        search({-1, -2})

    msg = str(excinfo.value)
    assert "all({n + m > 0 for n in numbers for m in numbers})" in msg


class Player:
    user: str


class CPU(Player):
    def __init__(self) -> None:
        self.user = "CPU"


@check_contracts
def _is_cpu(player: Player) -> bool:
    return player.user == "CPU"


def test_class_not_instance_error() -> None:
    """Test that the additional suggestion is added when the class type is passed in as the
    argument instead of its instance

    This test is coupled to the suggestion's arbitrarily chosen text, hence should be updated
    when changing the suggestion text.
    """
    with pytest.raises(AssertionError) as excinfo:
        _is_cpu(Player)

    msg = str(excinfo.value)
    assert "Did you mean Player(...) instead of Player?" in msg


def test_subclass_not_instance_error() -> None:
    """Test that the additional suggestion is added when a subclass type is passed in as an
    argument instead of its instance

    This test is coupled to the suggestion's arbitrarily chosen text, hence should be updated
    when changing the suggestion text.
    """
    with pytest.raises(AssertionError) as excinfo:
        _is_cpu(CPU)

    msg = str(excinfo.value)
    assert "Did you mean CPU(...) instead of CPU?" in msg


def test_no_suggestion_instance_as_instance() -> None:
    """Test that the additional suggestion is not added when an unrelated type is passed in.

    This test is coupled to the suggestion's arbitrarily chosen text, hence should be updated
    when changing the suggestion text.
    """
    with pytest.raises(AssertionError) as excinfo:
        _is_cpu(str)

    msg = str(excinfo.value)

    part1, part2, part3 = "Did you pass in", "instead of", "(...)?"
    assert part1 not in msg
    assert part2 not in msg
    assert part3 not in msg


def test_invalid_typing_generic_argument() -> None:
    """Test that subclass checking on a type parameter that is typing's _GenericAlias does not
    throw an error (as issubclass does not take in a _GenericAlias as its second argument).
    """

    @check_contracts
    def unary(arg: List[str]) -> None:
        return

    with pytest.raises(AssertionError):
        unary(dict)


@pytest.mark.skipif(sys.version_info < (3, 9), reason="built-in generics not yet supported")
def test_invalid_built_in_generic_argument() -> None:
    """Test that subclass checking on a type parameter that is a GenericAlias does not
    throw an error (as issubclass does not take in a GenericAlias as its second argument).
    """

    @check_contracts
    def unary(arg: list[str]) -> None:
        return

    with pytest.raises(AssertionError):
        unary(dict)
