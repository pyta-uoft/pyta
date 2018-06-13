from python_ta.util.monad import Failable
from nose.tools import eq_


def add4(a, b, c, d):
    return a + b + c + d


def test_monad():
    a = Failable(1)
    b = Failable(2)
    c = Failable(3)
    d = Failable(4)

    f = a >> add4
    eq_(f(2, 3, 4), 10)

    g = b >> f
    eq_(g(3, 4), 10)

    h = c >> g
    eq_(h(4), 10)

    i = d >> h
    eq_(i, 10)

    j = (d >> (c >> (b >> (a >> add4))))
    eq_(j, 10)
