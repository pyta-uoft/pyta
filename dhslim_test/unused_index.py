"""this is an error"""
import python_ta


def num_items(lst):
    """Return the numbers of items."""
    s = 0
    for i in range(len(lst)):
        s += 1

    return s

# def num_items1(lst):
#     """Return the numbers of items."""
#     s = 0
#     for i in range(len(lst)):
#         # i = lst[i]
#         for i in range(len(lst[i])):
#             s += 1
#     return s
#what if lst is a lst of lst
#professor when first gave the assignment said it is a list of numbers look at the function he gave only makes sense that way
# for i in range(lst[i]) makes sense
python_ta.check_all()

# unsused index i is covered already by error
# W0612 (unused-variable) so no need to worry about this
