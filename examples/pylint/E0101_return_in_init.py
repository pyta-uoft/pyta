class Animal:
    """An animal in the zoo.

    === Public Attributes ===
    @type name: str
    """
    def __init__(self: Animal, name: str) -> None:
        self.name = name
        return True  # Error on this line
