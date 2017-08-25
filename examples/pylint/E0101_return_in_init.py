class Animal:
    """An animal in the zoo."""

    def __init__(self, name: str) -> None:
        self._name = name
        return True  # Error on this line
