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


# Test that postcondition checks regarding function return values pass and fail as expected
@check_contracts
def _get_double_valid(num: int) -> int:
    """
    Return twice the number passed as the argument.

    Postcondition: $return_value == num * 2
    """
    return num * 2


@check_contracts
def _get_double_invalid(num: int) -> int:
    """
    Return a number that is not twice the number passed as the argument.

    Postcondition: $return_value == num * 2
    """
    return (num * 2) + 1


def test_get_double_valid() -> None:
    """Test that calling the valid implementation of _get_double succeeds."""
    assert _get_double_valid(5) == 10


def test_get_double_invalid() -> None:
    """Test that calling the invalid implementation of _get_double raises an AssertionError for failing postcondition
    check.
    """
    with pytest.raises(AssertionError) as excinfo:
        _get_double_invalid(5)

    msg = str(excinfo.value)
    assert "$return_value == num * 2" in msg


# Test that postcondition checks involving function parameters pass and fail as expected
@check_contracts
def _add_to_set_valid(num_set: Set[int], new_num: int) -> None:
    """
    Add a number to the provided set if the number does not already exist in the set.

    Postconditions:
        - new_num in num_set
    """
    if new_num not in num_set:
        num_set.add(new_num)


@check_contracts
def _add_to_set_invalid(num_set: Set[int], new_num: int) -> None:
    """
    Add new_num to the num_set. This is implemented incorrectly to make the postcondition check fail.

    Postconditions:
        - new_num in num_set
    """
    if new_num in num_set:
        num_set.add(new_num)


def test_add_to_set_valid() -> None:
    """Test that there are no errors when correctly adding a number to a set."""
    sample_set = {5, 4}
    _add_to_set_valid(sample_set, 1)
    assert 1 in sample_set


def test_add_to_set_invalid() -> None:
    """Test that the attempt to add a number to a set using _add_to_set_invalid raises an AssertionError."""
    sample_set = {1, 2}

    with pytest.raises(AssertionError) as excinfo:
        _add_to_set_invalid(sample_set, 5)

    msg = str(excinfo.value)
    assert "new_num in num_set" in msg


# Test that postcondition checks that use custom functions in scope pass and fail as expected
@check_contracts
def _get_even_nums_valid(lst: List[int]) -> List[int]:
    """
    Return a list of all even numbers in the input list.

    Postcondition: is_even($return_value)
    """
    return [num for num in lst if num % 2 == 0]


@check_contracts
def _get_even_nums_invalid(lst: List[int]) -> List[int]:
    """
    Return a list of all odd numbers in the input list, which should cause the postcondition check to fail.

    Postcondition: is_even($return_value)
    """
    return [num for num in lst if num % 2 != 0]


def test_get_even_nums_valid() -> None:
    """Test that _get_even_nums_valid correctly retrieves all even numbers in a list."""
    assert is_even(_get_even_nums_valid([4, 3, 2, 5, 6, 8, 1]))


def test_get_even_nums_invalid() -> None:
    """Test that the incorrect implementation of _get_even_nums raises an AssertionError because of the failure of
    the postcondition check.
    """

    with pytest.raises(AssertionError) as excinfo:
        _get_even_nums_invalid([5, 4, 3, 2, 1, 0, 5])

    msg = str(excinfo.value)
    assert "is_even($return_value)" in msg


# Test that a function returning a custom object successfully checks for postconditions
class Rectangle:
    def __init__(self, width: int, height: int):
        self.width = width
        self.height = height


@check_contracts
def _zero_rectangle_invalid() -> Rectangle:
    """
    Return a rectangle with non-zero width and height.

    Postconditions:
        - $return_value.width == 0
        - $return_value.height == 0
    """
    return Rectangle(5, 6)


@check_contracts
def _zero_rectangle_valid() -> Rectangle:
    """
    Return a rectangle with 0 width and height.

    Postconditions:
        - $return_value.width == 0
        - $return_value.height == 0
    """
    return Rectangle(0, 0)


def test_zero_rectangle_invalid() -> None:
    """Test that an error is raised when calling the incorrect implementation of _zero_rectangle."""

    with pytest.raises(AssertionError) as excinfo:
        _zero_rectangle_invalid()

    msg = str(excinfo.value)
    assert "$return_value.width == 0" in msg


def test_zero_rectangle_valid() -> None:
    """Test that postcondition checks pass for the valid implementation of _zero_rectangle."""
    rect = _zero_rectangle_valid()
    assert rect.width == 0 and rect.height == 0


# Use the legal variable name used to refer to the return value of the function by PyTA as a variable inside
# the function to ensure a new name is generated which does not cause collision.
@check_contracts
def _get_quotient(number: int) -> int:
    """
    Return the quotient obtained on dividing the number by 10.

    Postcondition: $return_value % 10 == 0
    """
    __function_return_value__ = 0

    while number > 0:
        number -= 10
        __function_return_value__ += 1

    return __function_return_value__


def test_get_quotient_valid() -> None:
    """Test that postcondition check passes when _get_quotient returns a multiple of 10."""
    assert _get_quotient(200) % 10 == 0


def test_get_quotient_invalid() -> None:
    """Test that an error is raised when _get_quotient returns a value that is not a multiple of 10."""
    with pytest.raises(AssertionError) as excinfo:
        _get_quotient(120)

    msg = str(excinfo.value)
    assert "$return_value % 10 == 0" in msg


# Test both pre and post conditions in a function
@check_contracts
def _get_quotient_with_pre_and_post(number: int) -> int:
    """
    Perform the same task as _get_quotient but this time ensure the input is a multiple of 100.

    Precondition: number % 100 == 0
    Postcondition: $return_value % 10 == 0
    """
    # Deliberately create a case in which precondition check passes but postcondition check does not
    if number == 400:
        return 4

    return _get_quotient(number)


def test_get_quotient_with_pre_and_post_valid() -> None:
    """Test the quotient on division by 10 is successfully returned for a multiple of 100."""
    assert _get_quotient_with_pre_and_post(500) % 10 == 0


def test_get_quotient_with_pre_and_post_invalid_input() -> None:
    """Test that an AssertionError is raised when a number that is not a multiple of 100 is provided as the input
    to _get_quotient_with_pre_and_post.
    """
    with pytest.raises(AssertionError) as excinfo:
        _get_quotient_with_pre_and_post(150)

    msg = str(excinfo.value)
    assert "number % 100 == 0" in msg


def test_get_quotient_with_pre_and_post_invalid_output() -> None:
    """Test that an AssertionError is raised when a number that is not a multiple of 10 is returned from
    _get_quotient_with_pre_and_post. In this case, the precondition check should pass but postcondition check should
    fail.
    """
    with pytest.raises(AssertionError) as excinfo:
        _get_quotient_with_pre_and_post(400)

    msg = str(excinfo.value)
    assert "$return_value % 10 == 0" in msg


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
