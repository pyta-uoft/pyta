from typing import *
from typing import TupleMeta, CallableMeta, _ForwardRef
# from python_ta.transforms.type_inference_visitor import main
from python_ta.typecheck.base import *
from python_ta.transforms.type_inference_visitor import *
from python_ta.typecheck.base import TypeConstraints
from nose import SkipTest
from nose.tools import eq_
import test_unify

src0 = '''
''[0]
'''

src1 = '''
a = 1
b = 2

c = a + b

def f(x):
    return x + 5

class A:
    x: int

    def __init__(self, a: int) -> None:
        self.x = a

    def sing(self) -> str:
        return 'david is cool'

lst = [2, 3, 4, 5]
'''


def test():
    tc = TypeConstraints()
    ti = TypeInferer()
    ast_mod, ti = main(src1)
    print(ast_mod)
    print(ti.type_constraints)

    assert False
