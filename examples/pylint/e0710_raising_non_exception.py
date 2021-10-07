class NotAnException:
    """This class does not inherit from BaseException."""
    pass

raise NotAnException()
