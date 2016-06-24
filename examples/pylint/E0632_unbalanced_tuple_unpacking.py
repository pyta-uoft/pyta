def set_values():
    """@rtype: tuple
    """
    var1 = 1
    var2 = 2
    return var1, var2

one, two, three = set_values()  # Error on this line. 2 on the
                                # right side but only 3 on the
                                # left.
