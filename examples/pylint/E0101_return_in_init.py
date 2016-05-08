"""pylint: return in init

"""


class Animal:
    """An animal in the zoo.
    """
    def __init__(self, name):
        self.name = name
        return True

    def is_animal(self):
        """
        @rtype: bool
        """
        return isinstance(self.name, str)

    def getter(self):
        """
        @rtype: str
        """
        return self.name

