class RandomClass():
    """This class doesn't inherit from BaseException."""
    pass


try:
    n = 5 / 0  # Will throw a ZeroDivisionError
except RandomClass:
    print('The above does not inherit from BaseException')
except ZeroDivisionError:
    print('Will not be reached due to erroring out earlier')