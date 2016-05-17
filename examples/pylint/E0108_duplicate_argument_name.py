"""pylint: duplicate argument name

"""

def add(lst, lst):
    """
    @type lst: list
    @type lst: list
    @rtype: int
    """
    temp = 0
    for item in lst:
        temp += item
    return temp

