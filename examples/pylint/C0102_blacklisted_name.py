"""pylint: blacklisted name

"""

def pos(obj):
    """
    @type obj: int
    @rtype: bool
    """
    foo = obj
    if foo < 0:
        return False
    else:
        return True
