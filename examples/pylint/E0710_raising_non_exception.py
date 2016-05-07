class ExceptionWithNoBaseClass:
    def __init__(self):
        pass

def throw_exception():
    raise ExceptionWithNoBaseClass()
