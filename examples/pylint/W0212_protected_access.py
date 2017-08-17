class MyClass:
    def __init__(self) -> None:
        self._num = 42

c = MyClass()
print(c._num)  # Error on this line: access of protected member `c._num`
