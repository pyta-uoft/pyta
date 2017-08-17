class MyClass:
    def __init__(self) -> None:
        pass

    def methodA(not_self) -> None:  # Bad (should be 'self')
        pass

    def methodB(self) -> None:  # Good
        pass
