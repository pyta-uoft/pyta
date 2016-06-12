class ClassA:
    def __init__(self):
        pass


class Parent:
    def __init__(self):
        pass


class Child(Parent):
    def __init__(self):
        ClassA.__init__(self)  # Not a child of class A