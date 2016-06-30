class ClassWithNoExceptionParent():
    """This class doesn't inherit from BaseException."""
    pass


raise ClassWithNoExceptionParent()
