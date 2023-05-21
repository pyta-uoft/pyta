"""Pointless Exception Statement Example"""
# The exception below is not raised, assigned, nor returned for use anywhere in this file.
# Note: ValueError is a subclass of Exception (it is a more specific type of exception in Python).


def reciprocal(num: float) -> float:
    """Return 1 / num."""
    if num == 0:
        ValueError('num cannot be 0!')  # Error on this line
    else:
        return 1 / num
