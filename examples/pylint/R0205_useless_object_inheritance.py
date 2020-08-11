class Animal(object):  # Error on this line
    """Abstract class to be implemented by all animals."""
    name: str

    def __init__(self, name: str) -> None:
        self.name = name