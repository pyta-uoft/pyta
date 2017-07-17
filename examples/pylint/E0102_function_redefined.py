def positive(obj):
    """
    @type obj: int
    @rtype: bool
    """
    return obj > 0


def positive(obj):  # Error on this line: Function redefined
    """
    @type obj: int
    @rtype: bool
    """
    return obj >= 0
