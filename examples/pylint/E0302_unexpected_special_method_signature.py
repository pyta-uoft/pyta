class A:
    def __init__(self) -> None:
        pass

    def __str__(self) -> str:  # Good, this is what is expected
        return 'string'


class B:
    def __init__(self) -> None:
        pass

    def __str__(self, a: str) -> str:  # Bad, Python won't know what to put in 'a'
        return 'string'
