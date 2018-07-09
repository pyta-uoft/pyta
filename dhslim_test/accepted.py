"""Illustrates accepted loop indexing."""
import python_ta


def sum_items(lst):
    """Return the sum of a list of numbers."""
    s = 0
    lst2 = [1, 2, 3]
    for i in range(len(lst)):
        s += lst2[i]

    return s


python_ta.check_all()
