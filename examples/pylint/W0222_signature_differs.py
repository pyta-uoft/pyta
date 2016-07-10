class Parent:
    def __init__(self):
        self.num = 2

    def return_num(self, multiple):
        return self.num * multiple


class Child(Parent):
    def __init__(self):
        Parent.__init__(self)

    def return_num(self):  # Missing argument (to keep signature identical)
        return 42
