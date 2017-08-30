from typing import List

def add(lst: List[int], lst: List[int]) -> int:
    """Calculate the sum of the elements in the given lists."""
    temp = 0
    for item in lst:
        temp += item
    return temp
