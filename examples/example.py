"""Example showing always returning in a loop."""


def loop():
    """always returning in a loop."""
    # always returning in a for loop
    for j in range(0, 2):
        if j > 3:
            return 1
        elif j > 2:
            return 3
        else:
            return 2
    # always returning in a while loop
    i = 1
    while i < 10:
        if i > 2:
            return 2
        for k in range(0, 3):
            if k < 2:
                k += 1
            return 2
        return 2


if __name__ == '__main__':
    loop()
