class Parent:
    def __init__(self):
        self.num = 1


class Child(Parent):
    def __init__(self):
        Parent.__init__(self)  # You must have this