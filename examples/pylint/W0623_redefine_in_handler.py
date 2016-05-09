"""pylint: Overridden exception handler.

"""

class error_class(Exception):
    def __int__(self, value): # Default __init__ of Exceptions has been overridden.
        self.value = value
        
