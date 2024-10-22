from __future__ import annotations

def add(lst: list[int], lst: list[int]) -> int:  # Error on this line
    """Calculate the sum of the elements in the given list."""
    temp = 0
    for item in lst:
        temp += item
    return temp
