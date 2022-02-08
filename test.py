from typing import Dict, List, Set
from python_ta.contracts import check_contracts
import pytest

def is_even(lst: List[int]) -> bool:
    return all([(not x & 1) for x in lst])

@check_contracts
def _is_even_sum(numbers: List[int]) -> int:
    """Return the sum of a list of numbers.

    Precondition: is_even(numbers)
    """
    return sum(numbers)

def test():
    try:
        _is_even_sum([1, 2])
    except AssertionError:
        print(1)

test()