from typing import List


def sum_items(lst: List[int]) -> int:
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(len(lst)):  # Error on this line. i is used only to index lst.
        s += lst[i]

    return s
