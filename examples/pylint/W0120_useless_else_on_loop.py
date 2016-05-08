"""pylint: useless else on loop

"""


def add(lst):
    """ Calculates the sum of the elements in the given list.

    @type lst: list
    @rtype: None
    """
    for item in lst:
        print(item)
    else:
        print("empty list")
