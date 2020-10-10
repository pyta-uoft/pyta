from typing import List, Dict, Set
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
        return {'one': 1}

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
        return 'string'

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
        _my_sum([1, 2, 'hello'])


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
        _my_sum_one_precondition('hi')


def test_my_sum_one_pre_violation() -> None:
    """Calling _my_sum_one_precondition one a value of the right type,
    but that violates the docstring precondition.
    """
    with pytest.raises(AssertionError) as excinfo:
        _my_sum_one_precondition([1])

    msg = str(excinfo.value)
    assert 'len(numbers) > 2' in msg

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
    assert 'is_even(numbers)' in msg


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
    assert 'all({n + m > 0 for n in numbers for m in numbers})' in msg
