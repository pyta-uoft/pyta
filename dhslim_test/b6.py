"""Illustrates correct? loop indexing."""
import python_ta


def add_index_number_to_items(lst):
    """Add index number to each item in the list"""
    s = 0
    for i in range(len(lst)):
        s += i

    return s


python_ta.check_all()
