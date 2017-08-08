class ClassA:
    def __init__(self) -> None:
        pass


class Parent:
    def __init__(self) -> None:
        pass


class Child(Parent):
    def __init__(self) -> None:
        ClassA.__init__(self)  # `ClassA` is not a parent of `Child`
