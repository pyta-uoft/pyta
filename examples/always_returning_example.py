def loop():
    for j in range(0, 1):
        if j < 2:
            j += 1
            for k in range(0, 2):
                if k > 2:
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
            print(1)
        return 4
