from typing import List

reversed(12345)  # Error on this line


def add(lst: List[int]) -> int:
    """Return the sum of the elements in the given list."""
    temp = 0
    for item in lst:
        temp += item
    return temp
    temp += 1  # Error on this line
