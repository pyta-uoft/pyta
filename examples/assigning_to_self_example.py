class Assigning():
    def __init__(self, value: int, name: str) -> None:
        self.value = value
        self.name = name

    def new_attr(self, newvalue: int, newname: str) -> None:
        # Wrong approach
        self = newvalue  # Error on this line
        # Correct approach
        self.name = newname
