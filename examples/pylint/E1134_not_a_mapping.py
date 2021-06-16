def func(a: int, b: float) -> None:
    pass


def call_func() -> None:
    a = 1
    func(**{'a': 10, 'b': 15.2})  # This works
    func(**a)  # Error on this line: non-mapping value 'a' used in a mapping context
