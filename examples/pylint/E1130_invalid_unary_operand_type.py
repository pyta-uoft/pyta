"""pylint: invalid unary operand type
"""

def info(age):
    """
    Return the info about my age.

    @type age: int
    @rtype: str
    """
    return "My age is" + age    # Error on this line

info(2)
