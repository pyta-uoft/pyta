"""Illustrates bad loop indexing. (shows error)"""
import python_ta


def sum_items(lst):
    """Return the sum of a list of numbers."""
    s = 0
    for i in range(len(lst)):
        s += lst[i]
        for j in range(len(lst)):
            s += lst[j]

    return s


python_ta.check_all()
