def number_choice(x: int, y: int, z: int) -> None:
    # Error on line below
    if (x or (y and z)) or (x % 53 == 7 or (z % x == y and z % 2 == 1) or ((x == y) and not (z == y))):
        print('nice choice of numbers')
    else:
        print('pick better numbers')
