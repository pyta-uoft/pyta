from typing import List, Tuple, Dict, Union
import astroid
from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfgs(src: str) -> Dict[Union[astroid.FunctionDef, astroid.Module], ControlFlowGraph]:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)
    return t.cfgs


def _extract_blocks(cfg: ControlFlowGraph) -> List[List[str]]:
    return [
        [s.as_string() for s in block.statements]
        for block in cfg.get_blocks()
    ]


def test_simple_class() -> None:
    src = """
    x = 0
    class A(CFGVisitor):
        pass
    print(x)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 1

    keys = list(cfgs)

    expected_blocks = [
        ['x = 0', 'pass', 'print(x)'],
        []
    ]
    assert expected_blocks == _extract_blocks(cfgs[keys[0]])


def test_compound_statement_in_class() -> None:
    src = """
    x = 0
    class A(CFGVisitor):
        if x > 5:
            print(x)
        else:
            print(y)
    print(z)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 1

    keys = list(cfgs)

    expected_blocks = [
        ['x = 0', 'x > 5'],
        ['print(x)'],
        ['print(z)'],
        [],
        ['print(y)']
    ]
    assert expected_blocks == _extract_blocks(cfgs[keys[0]])


def test_class_with_one_method() -> None:
    src = """
    class A(CFGVisitor):
        \"""This is a class docstring\"""
        c: int
        d: str

        def __init__(self) -> None:
            self.c = 10
            self.d = 'string'
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    keys = list(cfgs)

    expected_blocks_module = [
        ['c: int', 'd: str', '\ndef __init__(self) -> None:\n    '
                             'self.c = 10\n    self.d = \'string\''],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_method = [
        ['self'],
        ['self.c = 10', 'self.d = \'string\''],
        []
    ]
    assert expected_blocks_method == _extract_blocks(cfgs[keys[1]])


def test_class_with_multiple_method() -> None:
    src = """
    class A(CFGVisitor):
        \"""This is a class docstring\"""
        c: int
        d: str

        def __init__(self) -> None:
            self.c = 10
            self.d = 'string'

        def runner(self) -> str:
            return 'run'
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 3

    keys = list(cfgs)

    expected_blocks_module = [
        ['c: int', 'd: str', '\ndef __init__(self) -> None:\n    '
                             'self.c = 10\n    self.d = \'string\'',
         '\ndef runner(self) -> str:\n    '
         'return \'run\''],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_init = [
        ['self'],
        ['self.c = 10', 'self.d = \'string\''],
        []
    ]
    assert expected_blocks_init == _extract_blocks(cfgs[keys[1]])

    expected_block_method = [
        ['self'],
        ['return \'run\''],
        []
    ]
    assert expected_block_method == _extract_blocks(cfgs[keys[2]])
