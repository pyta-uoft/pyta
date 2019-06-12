from typing import List, Tuple
import astroid
from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfgs(src: str) -> ControlFlowGraph:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)
    return t.cfgs


def _extract_blocks(cfg: ControlFlowGraph) -> List[List[str]]:
    return [
        [s.as_string() for s in block.statements]
        for block in cfg.get_blocks()
    ]


def test_simple_function() -> None:
    src = """
    def func(x: int) -> None:
        print(x + 1)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    expected_blocks_module = [
        ['\ndef func(x:int)->None:\n    print(x + 1)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[0])

    expected_blocks_function = [
        ['\ndef func(x:int)->None:\n    print(x + 1)'],
        ['print(x + 1)'],
        []
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[1])


def test_simple_function_with_surrounding_statements() -> None:
    src = """
    x = 10
    def func(x: int) -> None:
        print(x + 1)
    print(x)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    expected_blocks_module = [
        ['x = 10', '\ndef func(x:int)->None:\n    print(x + 1)', 'print(x)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[0])

    expected_blocks_function = [
        ['\ndef func(x:int)->None:\n    print(x + 1)'],
        ['print(x + 1)'],
        []
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[1])


def test_multiple_simple_functions() -> None:
    src = """
    def func(x: int) -> None:
        print(x + 1)
    
    def func2(y: int) -> None:
        print(y - 1)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 3

    expected_blocks_module = [
        ['\ndef func(x:int)->None:\n    print(x + 1)',
         '\ndef func2(y:int)->None:\n    print(y - 1)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[0])

    expected_blocks_func = [
        ['\ndef func(x:int)->None:\n    print(x + 1)'],
        ['print(x + 1)'],
        []
    ]
    assert expected_blocks_func == _extract_blocks(cfgs[1])

    expected_blocks_func2 = [
        ['\ndef func2(y:int)->None:\n    print(y - 1)'],
        ['print(y - 1)'],
        []
    ]
    assert expected_blocks_func2 == _extract_blocks(cfgs[2])


def test_function_with_while() -> None:
    src = """
    def func(x: int) -> None:
        while x > 10:
            print(x)
        else:
            print(j)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    expected_blocks_module = [
        ['\ndef func(x:int)->None:\n    while x > 10:\n        '
         'print(x)\n    else:\n        print(j)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[0])

    expected_blocks_function = [
        ['\ndef func(x:int)->None:\n    while x > 10:\n        '
         'print(x)\n    else:\n        print(j)'],
        ['x > 10'],
        ['print(x)'],
        ['print(j)'],
        []
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[1])
