def missing_return() -> int:
    print("no return")


def missing_return_in_branch() -> int:
    a = 1
    if a > 3:
        print("no return")
    else:
        return a


def multiple_branches() -> int:
    if False:
        return 1
    elif True:
        print("no return")
    else:
        return 2


def try_except() -> int:
    try:
        print("try block")
    except Exception:
        print("except block")
