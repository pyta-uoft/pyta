class MyClass:
    def __init__(self):
        self._num = 42

c = MyClass()
# Should not be accssing the protected attribute:
print(c._num)
