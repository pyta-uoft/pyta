class Animal:
    """A carbon-based life form that eats and moves around."""
    _name: str

    def __init__(self, name: str) -> None:
        self._name = name


dog = Animal('Charly')
print(dog._name)  # Error on this line: Access of protected member `dog._name`
