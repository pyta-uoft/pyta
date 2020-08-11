from typing import List

def add(lst: List[int]) -> int:
    """Calculate the sum of the elements in the given list."""
    temp = 0
    for item in lst:
        temp += item
    return temp

print((lambda x: add(x))([1,2,3]))  # Error on this line
