from __future__ import annotations

def add(lst: list[int]) -> int:
    """Calculate the sum of the elements in the given list."""
    temp = 0
    for item in lst:
        temp += item
    temp  # Error on this line
