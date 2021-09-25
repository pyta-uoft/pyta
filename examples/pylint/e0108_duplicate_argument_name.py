from typing import List

def add(lst: List[int], lst: List[int]) -> int:  # Error on this line
    """Calculate the sum of the elements in the given list."""
    temp = 0
    for item in lst:
        temp += item
    return temp
