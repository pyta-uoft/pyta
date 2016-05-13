"""pylint: return in init

"""


class Animal:
    """An animal in the zoo.

    === Public Attributes ===
    @type name: str
    """
    def __init__(self, name):
        """
        @type self: Animal
        @type name: str
        @rtype: None
        """
        self.name = name
        return True

    def is_animal(self):
        """
        @type self: Animal
        @rtype: bool
        """
        return isinstance(self.name, str)

    def getter(self):
        """
        @type self: Animal
        @rtype: str
        """
        return self.name

