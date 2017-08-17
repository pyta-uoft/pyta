def loop() -> int:
    for j in range(0, 10):
        if j < 2:
            j += 1
            for k in range(0, 2):
                if k > 2:
                    for i in range(0, 5):
                        return 2
                    return 1
                else:
                    return 1
        elif j > 1:
            return 1
        else:
            j += 1
            return 1
    i = 0
    while i < 10:
        if i > 2:
            return 2
        else:
            i += 1
        return 4
    return 0
