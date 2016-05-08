"""pylint: duplicate key

"""


def check(obj):
    """
    @type obj: dict
    @rtype: bool
    """
    ex = {'runner1': '5km', 'runner1': '7km'}
    return ex == obj
