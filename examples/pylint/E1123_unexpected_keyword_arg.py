"""pylint: unexpected keyword arg
"""


def get_sum(a, b):
    """
    Return the sum of a and b

    @type a: int
    @type b: int
    @rtype: int
    """
    return a + b

get_sum(x=1, y=2)  # Error on this line
