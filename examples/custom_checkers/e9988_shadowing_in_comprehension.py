"""Example for E9988: shadowing-in-comprehension."""
from typing import List


# There are four different types of comprehensions:
# list comprehension, dict comprehension, set comprehension, and generator comprehension
# below are examples with each type of comprehensions in respective order


def num_lst(n: int) -> List[int]:
    """Return a list of integers from 0 to <n>, in that order."""
    return [n for n in range(n)]


def switch_dict(x: dict) -> dict:
    """Return a dictionary with keys and values switched."""
    return {y: x for x, y in x.items()}


def common_items(lst1: list, lst2: list) -> int:
    """Return the number of unique common items in <lst1> and <lst2>."""
    s = 0
    set1 = {s for s in lst1}
    for item in set1:
        if item in lst2:
            s += 1

    return s


def print_pos(lst: List[int]) -> None:
    """Print items in lst one by one if they are greater than 0."""
    for k in (k for k in lst if k > 0):
        print(k)
