class Example:
    def field(self, num: float) -> float:
        return num

    def __init__(self) -> None:
        self.field = 'Hiding the function with this string'

e = Example()
e.field(num)   # Error on this line
