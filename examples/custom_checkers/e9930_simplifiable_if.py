"""Examples for e9930_simplifiable_if_checker.py"""

def examples(x: int) -> int:
    """Demonstrates e9930_simplifiable_if_checker.py"""

    if x > 5:  # can be simplified 
        if x < 10:
            return x + 1

    if x < 4:
        x = 2
    elif x < -5:  # can be simplified 
        if x > -10:
            return x - 1
    
    if x < 4:  # cannot be simplified
        if x > 15:
            x = 2
    elif x < -5:  # cannot be simplified 
        if x > -10:
            return x - 1
    else:
        x = 5
    
    return x
