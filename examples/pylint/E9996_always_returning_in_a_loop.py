"""Example showing always returning in a loop."""


def loop():
    """always returning in a loop."""
    # always returning in a for loop
    for j in range(0, 2):
        j += 1
        print("sss")
        if j < 2:
            j += 1
        if j > 1:
            return 1
        else:
            j += 1
            return 1
    i = 0
    while i < 10:
        if i > 2:
            return 2
        else:
            print(1)
            return 4
        i += 1

