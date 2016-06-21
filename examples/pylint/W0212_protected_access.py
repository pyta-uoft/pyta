class MyClass:
    def __init__(self):
        self._num = 42

# Should not be calling the underscore field:
c = MyClass()
print(c._num)