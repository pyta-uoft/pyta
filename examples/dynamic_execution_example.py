from typing import Callable

def get_power_function(power: int) -> Callable[[int], int]:
    """Return a function which takes its argument to the <power>th power."""
    func = eval("lambda x: x ** {}".format(power))
    return func


power_func = get_power_function(10)
print(power_func(2))  # Prints 1024
