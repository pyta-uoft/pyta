"""This is an example of good indexing"""
import python_ta


def sum_even_items(lst):
    """Return the sum of every even index element in a list of numbers."""
    s = 0
    for i in range(len(lst)):
        if i % 2 == 0:
            s += lst[i]

    return s


python_ta.check_all()
