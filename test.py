"""
Hey
"""
def simplified_if():
    """
    Docstring
    """
    """exp = True
    x = 1
    if exp:
        #do something
        x = 4 + 3
    elif not exp: #else
        #do something
        x = 4 + 5
    return x
    """
    exp = True

    if exp: #1
        return True
    else:
        return False

    """if exp: #1
        return True
    elif not exp:
        return False
    """

    #nested if statements

if __name__ == "__main__":
    import python_ta
    python_ta.check_all()
