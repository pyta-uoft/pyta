"""Python script to use for testing that cfgs are only produced for functions when specified."""


a = 10
if a > 0:

    def foo() -> None:
        a = 5


for _ in range(5):

    def boo() -> None:
        print("boo")


def hoo() -> None:
    if a > 0:
        owl = "hoo"
