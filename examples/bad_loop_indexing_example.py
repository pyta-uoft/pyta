"""Examples of bad-loop-indexing"""
import python_ta

def sum_items(lst):
    """This is the simplest example. i is only used to index lst."""
    s = 0
    for i in range(len(lst)):
        s += lst[i]

    return s


def sum_two_items(lst1, lst2):
    """Two for-loops with bad index usage."""
    s = 0
    for i in range(len(lst1)):
        s += lst1[i]
    for j in range(len(lst2)):
        s += lst2[j]

    return s


def nested(lst):
    """Nested for-loops with bad index usage."""
    s = 0
    for i in range(len(lst)):
        s += lst[i]
        for j in range(len(lst)):
            s += lst[j]

    return s


def multiple_assign(lst):
    """For-loops containing multiple and simultaneous assignements."""
    for i in range(len(lst)):
        x = y = lst[i]
    for i in range(len(lst)):
        x, y = lst[i], lst[i] + 1


def index_in_if(lst):
    """For-loop containing an if statement with bad use of index"""
    s = 0
    for i in range(len(lst)):
        if lst[i] % 2 == 0:
            s += 1

    return s

# TODO: keep looking for more examples

python_ta.check_all()
