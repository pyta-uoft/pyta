"""C0116: Missing function docstring."""
def mystery(x):
    # Error on this line (no docstring)
    return (lambda y : x+y)

new_mystery = mystery(2)
print("What could be the output of new_mystery(2)?")
