def fun_testing():  # correct Arguments() 16
    """Stringy"""

    x = 1  # correct Assign() 4-9, Const() 8-9

    for i in range(4):  # correct
        pass  # correct

    try:
        if 3 is not None:
            pass
        elif 2 is not None:  # 27 is RHS of colon.
            fun_testing()
        else:
            pass
        x = 2  # correct
    except:  # correct
        return False  # correct
    else:
        pass
    finally:
        pass
