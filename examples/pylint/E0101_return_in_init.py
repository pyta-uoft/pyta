"""pylint: return in init
Need to disable Too few public methods
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
        return True  # Error on this line



