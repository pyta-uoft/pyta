def func( temp):
    """Return "positive" if <temp> is greater than 0. ELse return "negative".
    @type temp: int
    @rtype: str
    """
    if temp <= 0:
        return "neg"
    else:
        return "pos"
