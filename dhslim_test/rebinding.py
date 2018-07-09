"""Illustrates bad loop indexing. (shows error)"""
import python_ta


# def rebind1(lst):
#     """"""
#     s = 0
#     # bad
#     for i in range(len(lst)):
#         s += lst[i]
#         # good
#         for i in range(len(lst)):
#             i += 2
#             s += i
#     return s
#
# def sum_items(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # len(lst) == 0?
#     # bad
#     for i in range(len(lst)):
#         s += lst[i]
#         # bad
#         for i in range(len(lst)):
#             i = lst[i]
#             i = i//2 + 1
#             i += 2
#             lst[i] = 1
#             s += i
#
#     return s
#
# def _while(lst):
#     for i in range(len(lst)):
#         # good
#         while i in lst[i//2]:
#             return
#
# def sum_items4(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # bad
#     for i in range(len(lst)):
#         s += lst[i]
#         # correct
#         for i in range(len(lst)):
#             # i = (i + 1)//2
#             for i in range(lst[i//2]):
#                 s += i
#
#     return s

def sum_items45(lst):
    """Return the sum of a list of numbers."""
    s = 0
    # good
    for i in range(len(lst)):
        # i = lst[i] + 1
        i = (i + 1) // 3
        s += i
        # for i in range(lst[i//2]):
        #     s += i

    return s

# def sum_items5(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # good
#     for i in range(len(lst)):
#         i += 2
#         s += i
#
#     return s
#
# def sum_items6(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # bad
#     for i in range(len(lst)):
#         i = 2
#
#     return s
#
# def sum_items7(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # good
#     for i in range(len(lst)):
#         s += lst[i]
#         lst1 = [x for x in lst[i//2]]
#
#
#     return s
#
# def sum_items8(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # bad
#     for i in range(len(lst)):
#         s += lst[i]
#         lst1 = [x for x in lst[i]]
#

    # return s
#
# def sum_items2(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # bad
#     for i in range(len(lst)):
#         s += lst[i]
#         i = s
#         s += i
#
#     return s
# #
# #
# def sum_items3(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # bad
#     for i in range(len(lst)):
#         i = 2
#         i += 3
#         i += 4
#         i += 2
#         # i = i + 2 so i on the right side
#         s += i
#
#     return s

# function inside a function
# def:
#     def:

python_ta.check_all()
