def add(lst):
    """ Calculates the sum of the elements in the given list.

    @type lst: list
    @rtype: int
    """
    temp = 0
    for item in lst:
        temp += item
    break  # Error on this line
    return temp
