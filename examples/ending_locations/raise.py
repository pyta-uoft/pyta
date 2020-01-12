def f(b):
    if b:
        raise ValueError
    else:
        raise BaseException('error')
