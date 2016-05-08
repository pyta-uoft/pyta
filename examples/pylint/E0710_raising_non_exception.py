class ClassWithNoExceptionParent:
    def __init__(self):
        pass

def throw_exception():
    raise ClassWithNoExceptionParent()