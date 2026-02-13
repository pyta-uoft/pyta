"""Example for E9980 invalid precondition syntax checker"""


def demo_function(x: int, y: int) -> int:
    """
    Demonstrates e9980_invalid_precondition_syntax

    Preconditions:
       - x !== 0  # error on this line
       - y != 0  # no error on this line
    """
    return x//y
