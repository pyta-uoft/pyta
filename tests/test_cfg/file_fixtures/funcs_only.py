"""Python script to use for testing that cfgs are only produced for functions when specified."""

a = 5


class MyClass:
    def foo(self) -> None:
        print("method")


def foo() -> None:
    a = 5


def boo() -> None:
    print("boo")


def hoo() -> None:
    if a > 0:
        owl = "hoo"
