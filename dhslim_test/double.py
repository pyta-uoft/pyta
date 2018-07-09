"""Illustrates bad loop indexing."""
import python_ta


def sum_items(lst1, lst2):
    """Return the sum of the numbers in two lists."""
    s = 0
    for i in range(len(lst1)):
        s += lst1[i]
    for j in range(len(lst2)):
        s += lst2[j]

    return s


python_ta.check_all()
