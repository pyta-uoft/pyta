"""Example for E9984: for-target-subscript."""
from typing import List, Tuple


def example1(lst: List[int]) -> int:
    s = 0
    for lst[0] in lst:  # Error on this line. lst[0] is highlighted.
        s += lst[0]
    return s


def example2(lst: List[int]) -> List[int]:
    s = []
    for lst[0:1] in lst:  # Error on this line. lst[0:1] is highlighted.
        s += lst[0:1]
    return s


def example3(lst: List[Tuple[int]]) -> int:
    s = 0
    for lst[0], i in lst:  # Error on this line. lst[0] is highlighted.
        s += lst[0] * i
    return s
