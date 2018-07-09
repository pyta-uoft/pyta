# """not an error.(but shows error need to fix fixed)"""
# import python_ta
#
#
# def sum_items(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     for i in range(len(lst)):
#         # AugAssign but lst[i] on the left side (mutation)
#         # this is not an error
#         # take i and access the memory at lst[i]
#         lst[i] += 1
#     # this is diff from
#     # for x in lst:
#     #     x += 1
#
#     return s
#
#
# python_ta.check_all()


"""Shows a correct usage of index in a loop"""
import python_ta


def zero_items2(lst1, lst2):
    """Replace all elements of <lst1> and <lst2> with zeros."""
    for i in range(len(lst1)):
        lst1[i], lst2[i] = 0, 0


python_ta.check_all()






# """Shows a correct usage of index in a loop"""
# import python_ta
#
#
# def sum_items(lst):
#     """Return the sum of a list of numbers."""
#     s = 0
#     # a = 1
#     # b = 2
#     for i in range(len(lst)):
#         # AugAssign but lst[i] on the left side (mutation)
#         # this is not an error
#         # take i and access the memory at lst[i]
#         b, lst[i] = 1, 2
#     # this is diff from
#     # for x in lst:
#     #     x += 1
#
#     return s
#
#
# python_ta.check_all()
