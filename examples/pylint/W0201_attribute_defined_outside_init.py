class MyClass:
    def __init__(self):
        self.num = 1

c = MyClass()
c.other_num = 2  # This should be defined in __init__ first
