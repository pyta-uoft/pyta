"""Examples for E9996 one-iteration."""


def buggy_search(numbers: list[int], x: int) -> bool:
    """Return whether numbers contains x (buggy version)."""
    for number in numbers:
        if number == x:
            return True
        else:
            return False


def loop() -> int:
    """A more complex example."""
    for j in range(0, 10):  # loop 1 iterates only once
        if j < 2:
            j += 1
            for k in range(0, 2):  # loop could iterate more than once
                if k > 2:
                    for i in range(0, 5):
                        break  # loop exits in the first iteration
                    return 1
                else:
                    k += 1
        elif j > 1:
            return 1
        else:
            j += 1
            break
        i = 0
        while i < 10:  # loop iterates only once
            if i > 2:
                break
            else:
                i += 1
            return 4
        return 0  # loop 1 will always end up returning
