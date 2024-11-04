def func(x: int) -> int:
    '''
    Preconditions:
        - x > 10
    '''
    a = 10
    if x > 0:   # by function precondition, this condition is True
        a = 20  # `a` is reassigned before first use
    return a
