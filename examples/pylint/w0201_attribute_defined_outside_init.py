class SomeNumbers:
    """A class to store some numbers."""
    num: int

    def __init__(self) -> None:
        self.num = 1

    def set_other_num(self, other_num: int) -> None:
        self.other_num = other_num
