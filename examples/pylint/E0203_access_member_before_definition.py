class Animal:
    """A carbon-based life form that eats and moves around."""

    def __init__(self, name: str) -> None:
        print(self._name)  # Haven't defined `self._name` yet, can't use
        self._name = name
