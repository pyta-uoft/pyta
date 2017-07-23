def get_power_function(power):
    """Return a function which takes its argument to the <power>th power."""
    func = eval("lambda x: x ** {}".format(power))
    return func


if __name__ == '__main__':
    power_func = get_power_function(10)
    print(power_func(2))  # Prints 1024
