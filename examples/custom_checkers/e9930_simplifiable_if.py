"""Examples for e9930_simplifiable_if_checker.py"""

def examples(x: int) -> int:
    """Demonstrates e9930_simplifiable_if_checker.py"""

    if x > 5:  # can be simplified 
        if x < 10:
            return x + 1
    elif x < -5:  # can be simplified 
        if x > -10:
            return x - 1
    elif x == 0:  # cannot be simplified
        return 0
    return x
