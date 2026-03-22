"""Example for E9981 invalid postcondition syntax checker"""


def demo_function(x: int, y: int) -> int:
    """Demonstrates e9981_invalid_postcondition_syntax

    Postconditions:
       - $return_value > = 0 # error on this line
       - $return_value != y  # no error on this line
    """
    return max(0, x // y)
