import python_ta

def multiple_assign(lst):
    """For-loop containing a multiple assignement."""
    for i in range(len(lst)):
        x = y = lst[i]

def multiple_assign2(lst):
    """For-loop containing a multiple assignement."""
    for i in range(len(lst)):
        x, y = lst[i], i

def index_minus_one(lst):
    """For-loop containing a multiple assignement."""
    for i in range(len(lst)):
        x = y = lst[i-1]


python_ta.check_all()
