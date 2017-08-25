class NotAnException:
    """This class does not inherit from BaseException."""
    pass

try:
    n = 5 / 0
except NotAnException:  # Error on this line: NotAnException does not inherit
    pass                # from BaseException
