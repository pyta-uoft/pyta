"""pylint: misplaced comparision constant

"""

def pos(obj):
    """
    @type obj: int
    @rtype: bool
    """
    if 0 > obj:
        return False
    else:
        return True
