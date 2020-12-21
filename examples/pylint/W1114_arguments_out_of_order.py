def f(x: int, y: int, z: int) -> int:
    return x + y + z


def g(n: int) -> int:
    x = n
    y = n * 2
    z = n * 3

    return f(y, z, x)  # Error on this line
