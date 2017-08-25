class Animal:
    """An animal in the zoo."""

    def __init__(self, name: str) -> None:
        self._name = name
        return True  # Error on this line

dog = Animal('Charly')
print(dog._name)  # Error on this line: Access of protected member `dog._name`
