"""pylint: unexpected keyword arg
"""


def get_sum(a, b = 2):
    """
    Return the sum of a and b.

    @type a: int
    @type b: int
    @rtype: int
    """
    return a + b

get_sum(1, a = 2, b = 2)  # Error on this line
