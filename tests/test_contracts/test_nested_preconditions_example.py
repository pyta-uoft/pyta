from python_ta.contracts import check_contracts


@check_contracts
def my_condition1(y: int):
    """
    Preconditions:
    - my_condition2(y)
    """
    return y > 0


@check_contracts
def my_condition2(x: int):
    """
    Preconditions:
    - x > 0
    """
    return x > 0


@check_contracts
def my_function(z: int):
    """

    Preconditions:
    - my_condition1(z)
    """
    return z
