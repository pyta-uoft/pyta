class C:
    def __init__(self) -> None:
        self.num = 5

    @staticmethod
    def method(self) -> int:  # Static methods do not have a 'self'
        self.num += 1
