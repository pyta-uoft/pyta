class Animal:
    """A carbon-based life form that eats and moves around."""

    def __init__(self, name: str) -> None:
        self._name = name
        return True  # Error on this line
