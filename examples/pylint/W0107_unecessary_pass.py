"""pylint: expression not assigned
Note: doesn't work
"""


def add(lst):
    """
    @type lst: list
    @rtype: int
    """
    temp = 0
    for item in lst:
        temp += item
        pass
    return temp
