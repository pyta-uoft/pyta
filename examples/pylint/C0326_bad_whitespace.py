def func( temp):
    """Print "positive" if <temp> is greater than 0. ELse print "negative".
    @type temp: int
    @rtype: str
    """
    if temp <= 0:
        return "neg"
    else:
        return "pos"
