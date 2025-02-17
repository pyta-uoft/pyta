"""Python script to use for testing whether cfgs were generated correctly"""


def foo() -> None:
    for i in range(1, 10):
        if i < 5:
            print("hi")


def func_with_while() -> None:
    """A function with a while loop"""
    a = 1
    while a < 100:
        print(a)
        a += 1


def func_with_unreachable() -> int:
    """A function with unreachable code"""
    a = 1
    return a * 10
    a = 2
