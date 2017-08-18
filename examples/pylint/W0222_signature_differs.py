class Parent:
    def __init__(self) -> None:
        self.num = 2

    def return_num(self, multiple: float) -> float:
        return self.num * multiple


class Child(Parent):
    def __init__(self) -> None:
        Parent.__init__(self)

    def return_num(self) -> float:  # Method signature differs from Parent
        return 42
