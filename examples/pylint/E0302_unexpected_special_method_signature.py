class Animal:
    """A carbon-based life form."""

    def __init__(self, name: str) -> None:
        self._name = name

    def __str__(self, unexpected_argument: str) -> str:  # Error on this line
        return unexpected_argument
