"""pylint: bad builtin

"""


def pos(obj):
    """
    @type obj: int
    @rtype: bool
    """
    if obj < 0:
        return False
    else:
        return True

if __name__ == '__main__':
    filter(pos, [1, -4, 5])
