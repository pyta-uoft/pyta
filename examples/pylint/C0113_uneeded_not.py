"""pylint: uneeded not

"""

def is_true():
    """
    @type obj: int
    @rtype: bool
    """
    temp = 5
    if temp is not not True:
        return False
    else:
        return True
