"""
Hey
"""

def examples():
    """
    Docstring
    """
    if {1: 3}:
        return True
    if {}:
        return False
    if (3, 4):
        return False
    if 4 and 5:
        return False
    if 1 and 3:
        return True
    if 5:
        return True
    if 1:
        return False
    if 4 and 4 and 3 and 3 and 3:
        return True
    if 1 and 2:
        if 3 and 4:
            if 5 and 2:
                if "hello":
                    return True

if __name__ == "__main__":
    import python_ta
    python_ta.check_all('examples/pylint/R1702_too_many_nested_blocks.py')
    #python_ta.check_all()
