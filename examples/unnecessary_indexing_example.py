"""Example for E9994: unnecessary-indexing."""
from typing import List


def sum_items(lst: List[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(len(lst)):  # Error on this line (i is highlighted).
        s += lst[i]

    return s


def sum_items2(lst: List[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(0, len(lst)):  # Error on this line (i is highlighted).
        s += lst[i]

    return s


def sum_items3(lst: List[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(0, len(lst), 1):  # Error on this line (i is highlighted).
        s += lst[i]

    return s


def sum_pairs(lst1: List[int], lst2: List[int]) -> int:
    """Return the sum of corresponding products of two list of numbers."""
    s = 0
    # NO error reported; the loop index is used to index lst2 as well.
    for i in range(len(lst1)):
        s += lst1[i] * lst2[i]

    return s
