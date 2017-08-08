class MyClass:
    def __init__(self) -> None:
        print(self.a)  # Haven't defined `self.a` yet, can't use
        self.a = 5
