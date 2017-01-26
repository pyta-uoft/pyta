from . import file_input
from io import StringIO
from tokenize import generate_tokens
import unittest


class ParserTest(unittest.TestCase):
    def check_suite(self, s):
        ts = list(generate_tokens(StringIO(s + '\n').readline))
        file_input.parse(ts)

    check_expr = check_suite

    def test_yield_statement(self):
        self.check_suite("def f(): yield 1")
        self.check_suite("def f(): yield")
        self.check_suite("def f(): x += yield")
        self.check_suite("def f(): x = yield 1")
        self.check_suite("def f(): x = y = yield 1")
        self.check_suite("def f(): x = yield")
        self.check_suite("def f(): x = y = yield")
        self.check_suite("def f(): 1 + (yield)*2")
        self.check_suite("def f(): (yield 1)*2")
        self.check_suite("def f(): return; yield 1")
        self.check_suite("def f(): yield 1; return")
        self.check_suite("def f(): yield from 1")
        self.check_suite("def f(): x = yield from 1")
        self.check_suite("def f(): f((yield from 1))")
        self.check_suite("def f(): yield 1; return 1")
        self.check_suite("def f():\n"
                         "    for x in range(30):\n"
                         "        yield x\n")
        self.check_suite("def f():\n"
                         "    if (yield):\n"
                         "        yield x\n")

    def test_await_statement(self):
        self.check_suite("async def f():\n await smth()")
        self.check_suite("async def f():\n foo = await smth()")
        self.check_suite("async def f():\n foo, bar = await smth()")
        self.check_suite("async def f():\n (await smth())")
        self.check_suite("async def f():\n foo((await smth()))")
        self.check_suite("async def f():\n await foo(); return 42")

    def test_async_with_statement(self):
        self.check_suite("async def f():\n async with 1: pass")
        self.check_suite("async def f():\n async with a as b, c as d: pass")


    def test_async_for_statement(self):
        self.check_suite("async def f():\n async for i in (): pass")
        self.check_suite("async def f():\n async for i, b in (): pass")


    def test_nonlocal_statement(self):
        self.check_suite("def f():\n"
                         "    x = 0\n"
                         "    def g():\n"
                         "        nonlocal x\n")
        self.check_suite("def f():\n"
                         "    x = y = 0\n"
                         "    def g():\n"
                         "        nonlocal x, y\n")

    def test_expressions(self):
        self.check_expr("foo(1)")
        self.check_expr("[1, 2, 3]")
        self.check_expr("[x**3 for x in range(20)]")
        self.check_expr("[x**3 for x in range(20) if x % 3]")
        self.check_expr("[x**3 for x in range(20) if x % 2 if x % 3]")
        self.check_expr("list(x**3 for x in range(20))")
        self.check_expr("list(x**3 for x in range(20) if x % 3)")
        self.check_expr("list(x**3 for x in range(20) if x % 2 if x % 3)")
        self.check_expr("foo(*args)")
        self.check_expr("foo(*args, **kw)")
        self.check_expr("foo(**kw)")
        self.check_expr("foo(key=value)")
        self.check_expr("foo(key=value, *args)")
        self.check_expr("foo(key=value, *args, **kw)")
        self.check_expr("foo(key=value, **kw)")
        self.check_expr("foo(a, b, c, *args)")
        self.check_expr("foo(a, b, c, *args, **kw)")
        self.check_expr("foo(a, b, c, **kw)")
        self.check_expr("foo(a, *args, keyword=23)")
        self.check_expr("foo + bar")
        self.check_expr("foo - bar")
        self.check_expr("foo * bar")
        self.check_expr("foo / bar")
        self.check_expr("foo // bar")
        self.check_expr("lambda: 0")
        self.check_expr("lambda x: 0")
        self.check_expr("lambda *y: 0")
        self.check_expr("lambda *y, **z: 0")
        self.check_expr("lambda **z: 0")
        self.check_expr("lambda x, y: 0")
        self.check_expr("lambda foo=bar: 0")
        self.check_expr("lambda foo=bar, spaz=nifty+spit: 0")
        self.check_expr("lambda foo=bar, **z: 0")
        self.check_expr("lambda foo=bar, blaz=blat+2, **z: 0")
        self.check_expr("lambda foo=bar, blaz=blat+2, *y, **z: 0")
        self.check_expr("lambda x, *y, **z: 0")
        self.check_expr("(x for x in range(10))")
        self.check_expr("foo(x for x in range(10))")
        self.check_expr("...")
        self.check_expr("a[...]")

    def test_simple_expression(self):
        # expr_stmt
        self.check_suite("a")

    def test_simple_assignments(self):
        self.check_suite("a = b")
        self.check_suite("a = b = c = d = e")


    def test_var_annot(self):
        self.check_suite("x: int = 5")
        self.check_suite("y: List[T] = []; z: [list] = fun()")
        self.check_suite("x: tuple = (1, 2)")
        self.check_suite("d[f()]: int = 42")
        self.check_suite("f(d[x]): str = 'abc'")
        self.check_suite("x.y.z.w: complex = 42j")
        self.check_suite("x: int")
        self.check_suite("def f():\n"
                         "    x: str\n"
                         "    y: int = 5\n")
        self.check_suite("class C:\n"
                         "    x: str\n"
                         "    y: int = 5\n")
        self.check_suite("class C:\n"
                         "    def __init__(self, x: int) -> None:\n"
                         "        self.x: int = x\n")

    def test_simple_augmented_assignments(self):
        self.check_suite("a += b")
        self.check_suite("a -= b")
        self.check_suite("a *= b")
        self.check_suite("a /= b")
        self.check_suite("a //= b")
        self.check_suite("a %= b")
        self.check_suite("a &= b")
        self.check_suite("a |= b")
        self.check_suite("a ^= b")
        self.check_suite("a <<= b")
        self.check_suite("a >>= b")
        self.check_suite("a **= b")

    def test_function_defs(self):
        self.check_suite("def f(): pass")
        self.check_suite("def f(*args): pass")
        self.check_suite("def f(*args, **kw): pass")
        self.check_suite("def f(**kw): pass")
        self.check_suite("def f(foo=bar): pass")
        self.check_suite("def f(foo=bar, *args): pass")
        self.check_suite("def f(foo=bar, *args, **kw): pass")
        self.check_suite("def f(foo=bar, **kw): pass")

        self.check_suite("def f(a, b): pass")
        self.check_suite("def f(a, b, *args): pass")
        self.check_suite("def f(a, b, *args, **kw): pass")
        self.check_suite("def f(a, b, **kw): pass")
        self.check_suite("def f(a, b, foo=bar): pass")
        self.check_suite("def f(a, b, foo=bar, *args): pass")
        self.check_suite("def f(a, b, foo=bar, *args, **kw): pass")
        self.check_suite("def f(a, b, foo=bar, **kw): pass")

        self.check_suite("@staticmethod\n"
                         "def f(): pass")
        self.check_suite("@staticmethod\n"
                         "@funcattrs(x, y)\n"
                         "def f(): pass")
        self.check_suite("@funcattrs()\n"
                         "def f(): pass")

        # keyword-only arguments
        self.check_suite("def f(*, a): pass")
        self.check_suite("def f(*, a = 5): pass")
        self.check_suite("def f(*, a = 5, b): pass")
        self.check_suite("def f(*, a, b = 5): pass")
        self.check_suite("def f(*, a, b = 5, **kwds): pass")
        self.check_suite("def f(*args, a): pass")
        self.check_suite("def f(*args, a = 5): pass")
        self.check_suite("def f(*args, a = 5, b): pass")
        self.check_suite("def f(*args, a, b = 5): pass")
        self.check_suite("def f(*args, a, b = 5, **kwds): pass")

        # function annotations
        self.check_suite("def f(a: int): pass")
        self.check_suite("def f(a: int = 5): pass")
        self.check_suite("def f(*args: list): pass")
        self.check_suite("def f(**kwds: dict): pass")
        self.check_suite("def f(*, a: int): pass")
        self.check_suite("def f(*, a: int = 5): pass")
        self.check_suite("def f() -> int: pass")

    def test_class_defs(self):
        self.check_suite("class foo():pass")
        self.check_suite("class foo(object):pass")
        self.check_suite("@class_decorator\n"
                         "class foo():pass")
        self.check_suite("@class_decorator(arg)\n"
                         "class foo():pass")
        self.check_suite("@decorator1\n"
                         "@decorator2\n"
                         "class foo():pass")

    def test_import_from_statement(self):
        self.check_suite("from sys.path import *")
        self.check_suite("from sys.path import dirname")
        self.check_suite("from sys.path import (dirname)")
        self.check_suite("from sys.path import (dirname,)")
        self.check_suite("from sys.path import dirname as my_dirname")
        self.check_suite("from sys.path import (dirname as my_dirname)")
        self.check_suite("from sys.path import (dirname as my_dirname,)")
        self.check_suite("from sys.path import dirname, basename")
        self.check_suite("from sys.path import (dirname, basename)")
        self.check_suite("from sys.path import (dirname, basename,)")
        self.check_suite(
            "from sys.path import dirname as my_dirname, basename")
        self.check_suite(
            "from sys.path import (dirname as my_dirname, basename)")
        self.check_suite(
            "from sys.path import (dirname as my_dirname, basename,)")
        self.check_suite(
            "from sys.path import dirname, basename as my_basename")
        self.check_suite(
            "from sys.path import (dirname, basename as my_basename)")
        self.check_suite(
            "from sys.path import (dirname, basename as my_basename,)")
        self.check_suite("from .bogus import x")

    def test_basic_import_statement(self):
        self.check_suite("import sys")
        self.check_suite("import sys as system")
        self.check_suite("import sys, math")
        self.check_suite("import sys as system, math")
        self.check_suite("import sys, math as my_math")

    def test_relative_imports(self):
        self.check_suite("from . import name")
        self.check_suite("from .. import name")
        # check all the way up to '....', since '...' is tokenized
        # differently from '.' (it's an ellipsis token).
        self.check_suite("from ... import name")
        self.check_suite("from .... import name")
        self.check_suite("from .pkg import name")
        self.check_suite("from ..pkg import name")
        self.check_suite("from ...pkg import name")
        self.check_suite("from ....pkg import name")

    def test_pep263(self):
        self.check_suite("# -*- coding: iso-8859-1 -*-\n"
                         "pass\n")

    def test_assert(self):
        self.check_suite("assert alo < ahi and blo < bhi\n")

    def test_with(self):
        self.check_suite("with open('x'): pass\n")
        self.check_suite("with open('x') as f: pass\n")
        self.check_suite("with open('x') as f, open('y') as g: pass\n")

    def test_try_stmt(self):
        self.check_suite("try: pass\nexcept: pass\n")
        self.check_suite("try: pass\nfinally: pass\n")
        self.check_suite("try: pass\nexcept A: pass\nfinally: pass\n")
        self.check_suite("try: pass\nexcept A: pass\nexcept: pass\n"
                         "finally: pass\n")
        self.check_suite("try: pass\nexcept: pass\nelse: pass\n")
        self.check_suite("try: pass\nexcept: pass\nelse: pass\n"
                         "finally: pass\n")

    def test_extended_unpacking(self):
        self.check_suite("*a = y")
        self.check_suite("x, *b, = m")
        self.check_suite("[*a, *b] = y")
        self.check_suite("for [*x, b] in x: pass")

    def test_raise_statement(self):
        self.check_suite("raise\n")
        self.check_suite("raise e\n")
        self.check_suite("try:\n"
                         "    suite\n"
                         "except Exception as e:\n"
                         "    raise ValueError from e\n")

    def test_list_displays(self):
        self.check_expr('[]')
        self.check_expr('[*{2}, 3, *[4]]')

    def test_set_displays(self):
        self.check_expr('{*{2}, 3, *[4]}')
        self.check_expr('{2}')
        self.check_expr('{2,}')
        self.check_expr('{2, 3}')
        self.check_expr('{2, 3,}')

    def test_dict_displays(self):
        self.check_expr('{}')
        self.check_expr('{a:b}')
        self.check_expr('{a:b,}')
        self.check_expr('{a:b, c:d}')
        self.check_expr('{a:b, c:d,}')
        self.check_expr('{**{}}')
        self.check_expr('{**{}, 3:4, **{5:6, 7:8}}')

    def test_argument_unpacking(self):
        self.check_expr("f(*a, **b)")
        self.check_expr('f(a, *b, *c, *d)')
        self.check_expr('f(**a, **b)')
        self.check_expr('f(2, *a, *b, **b, **c, **d)')
        self.check_expr("f(*b, *() or () and (), **{} and {}, **() or {})")

    def test_set_comprehensions(self):
        self.check_expr('{x for x in seq}')
        self.check_expr('{f(x) for x in seq}')
        self.check_expr('{f(x) for x in seq if condition(x)}')

    def test_dict_comprehensions(self):
        self.check_expr('{x:x for x in seq}')
        self.check_expr('{x**2:x[3] for x in seq if condition(x)}')
        self.check_expr('{x:x for x in seq1 for y in seq2 if condition(x, y)}')


if __name__ == '__main__':
    unittest.main()