def is_none(var1, var2):
    """Return None if first parameter is None, else return both parameters."""
    if var1 is None:
        return None
    else:
        return var1, var2

result = is_none(var1, var2)   # Error on this line since function is_none
                               # might return None.
