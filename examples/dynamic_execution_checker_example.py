"""Example showing a forbidden use of built-in function eval()."""

def greet(name):
    eval('a = 4')   # Error on this line.
