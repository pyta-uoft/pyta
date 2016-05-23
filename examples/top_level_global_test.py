"""example for global_variables_test
"""

ex = 1


def to_print():
    """ A test for top-level variables that are not constant using the global
    variables checker.

    @rtype: None
    """
    ex1 = 1
    print(ex1)

if __name__ == '__main__':
    to_print()
