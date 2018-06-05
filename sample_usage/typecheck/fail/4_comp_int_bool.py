# typecheck needs to handle inheritance properly for this example to work

x = 3
y = x


def f(a):
    return a == 'abc'


f(y)
