"""Example for E9994: unnecessary-indexing."""
from __future__ import annotations


def sum_items(lst: list[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(len(lst)):  # Error on this line (i is highlighted).
        s += lst[i]

    return s


def sum_items2(lst: list[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(0, len(lst)):  # Error on this line (i is highlighted).
        s += lst[i]

    return s


def sum_items3(lst: list[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(0, len(lst), 1):  # Error on this line (i is highlighted).
        s += lst[i]

    return s


def sum_pairs(lst1: list[int], lst2: list[int]) -> int:
    """Return the sum of corresponding products of two list of numbers."""
    s = 0
    # NO error reported; the loop index is used to index lst2 as well.
    for i in range(len(lst1)):
        s += lst1[i] * lst2[i]

    return s


def nested_sum(items: list[list[int]]) -> int:
    """Return a repeated sum of the items in the list."""
    s = 0
    for i in range(len(items)):  # Error on this line (i is highlighted).
        s += sum([2 * x for x in items[i]])
    return s


def nested_comprehension(items: list) -> None:
    """Illustrate this checker in a nested comprehension."""
    for i in range(len(items)):  # Error on this line (i is highlighted).
        print([[items[i] for _ in range(10)] for _ in [1, 2, 3]])


def nested_comprehensions2(items: list) -> None:
    """Illustrate this checker in a nested comprehension, where the
    loop variable is unused."""

    # NO error reported; j is initialized outside the loop.
    j = 0
    for _ in range(len(items)):
        print([[items[j] for _ in range(10)] for _ in [1, 2, 3]])


def nested_comprehensions3(items: list) -> None:
    """Illustrate this checker in a nested comprehension,

    where the index into the list is not defined."""
    # NO error reported; j is undefined.
    for _ in range(len(items)):
        print([[items[j] for _ in range(10)] for _ in [1, 2, 3]])


def nested_comprehensions4(items: list) -> None:
    """Illustrate this checker in a nested comprehension,
    where the index into the list is defined in an outer comprehension."""

    # NO error reported; j is undefined.
    for _ in range(len(items)):
        print([[items[j] for _ in range(10)] for j in [1, 2, 3]])


def loop_variable_reassigned(items: list[int]) -> int:
    """Illustrate this checker on a loop where the loop variable is reassigned
    in the loop body."""
    s = 0

    # NO error reported; the loop variable assignment i is unused,
    # but is not redundant.
    for i in range(len(items)):
        i = 0
        s += items[i]

    return s


def list_comp(lst: list) -> list:
    """Return all the items in lst in a new list."""
    return [lst[i] for i in range(len(lst))]  # Error on this line


def comp_binop(lst: list) -> list:
    """Return a list of all the items in lst multiplied by 2"""
    return [2 * lst[i] for i in range(len(lst))]  # Error on this line


def comp_var_unused(lst: list) -> list:
    """Index variable i is unused in the code, no unnecessary indexing performed"""

    # No error reported; index variable unused.
    return [lst[0] for i in range(len(lst))]
