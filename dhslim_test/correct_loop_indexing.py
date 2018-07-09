# """Illustrates bad loop indexing."""
# import python_ta
#
#
# def sum_items(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     for i in range(len(lst)):
#         s += lst[i]
#
#     return s
#
#
# python_ta.check_all()


"""Illustrates correct loop indexing."""
import python_ta


def sum_items(lst):
    """Return the sum of a list of numbers."""
    s = 0
    for x in lst:
        s += x

    return s


python_ta.check_all()
