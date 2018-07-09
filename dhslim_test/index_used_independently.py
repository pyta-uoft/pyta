"""index used independently (correct)"""
import python_ta


def sum_second_items(lst):
    """Return the sum of every second number in a list of numbers."""
    s = 0
    for i in range(len(lst)):
        s += lst[i]
        if i % 2 == 0:
            s += lst[i]

    return s




"""index used independently (correct)"""
# not useful example

def sum_second_items1(lst):
    """Return the sum of every second number in a list of numbers."""
    s = 0
    for i in range(len(lst)):
        s += lst[i//2]

    return s


python_ta.check_all()
