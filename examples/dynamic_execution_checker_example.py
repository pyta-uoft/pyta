"""Example showing a forbidden use of built-in function eval()."""


def greet():
    eval('a = 4')   # Error on this line.
    compile()
