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


def _extract_edges(cfg: ControlFlowGraph) -> List[List[List[str]]]:
    edges = [[edge.source.statements, edge.target.statements] for edge in cfg.get_edges()]
    expanded_edges = [[[source.as_string() for source in edge[0]],
                      [target.as_string() for target in edge[1]]]
                      for edge in edges]
    return expanded_edges


def test_simple_function() -> None:
    src = """
    def func(x: int) -> None:
        print(x + 1)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    keys = list(cfgs)

    expected_blocks_module = [
        ['\ndef func(x: int) -> None:\n    print(x + 1)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_function = [
        ['x: int'],
        ['print(x + 1)'],
        []
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[keys[1]])


def test_simple_function_with_surrounding_statements() -> None:
    src = """
    x = 10
    def func(x: int) -> None:
        print(x + 1)
    print(x)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    keys = list(cfgs)

    expected_blocks_module = [
        ['x = 10', '\ndef func(x: int) -> None:\n    print(x + 1)', 'print(x)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_function = [
        ['x: int'],
        ['print(x + 1)'],
        []
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[keys[1]])


def test_multiple_simple_functions() -> None:
    src = """
    def func(x: int) -> None:
        print(x + 1)
    
    def func2(y: int) -> None:
        print(y - 1)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 3

    keys = list(cfgs)

    expected_blocks_module = [
        ['\ndef func(x: int) -> None:\n    print(x + 1)',
         '\ndef func2(y: int) -> None:\n    print(y - 1)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_func = [
        ['x: int'],
        ['print(x + 1)'],
        []
    ]
    assert expected_blocks_func == _extract_blocks(cfgs[keys[1]])

    expected_blocks_func2 = [
        ['y: int'],
        ['print(y - 1)'],
        []
    ]
    assert expected_blocks_func2 == _extract_blocks(cfgs[keys[2]])


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

    keys = list(cfgs)

    expected_blocks_module = [
        ['\ndef func(x: int) -> None:\n    while x > 10:\n        '
         'print(x)\n    else:\n        print(j)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_function = [
        ['x: int'],
        ['x > 10'],
        ['print(x)'],
        ['print(j)'],
        []
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[keys[1]])


def test_simple_function_with_return() -> None:
    src = """
    def func(x: int) -> None:
        print(x + 1)
        return
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    keys = list(cfgs)

    expected_blocks_module = [
        ['\ndef func(x: int) -> None:\n    print(x + 1)\n    return'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_function = [
        ['x: int'],
        ['print(x + 1)', 'return'],
        []
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[keys[1]])


def test_function_with_if_and_return() -> None:
    src = """
    def func(x: int) -> None:
        if x > 10:
            return
        else:
            print(x - 1)
        print(x)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    keys = list(cfgs)

    expected_blocks_module = [
        ['\ndef func(x: int) -> None:\n    if x > 10:\n        '
         'return\n    else:\n        print(x - 1)\n    print(x)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_function = [
        ['x: int'],
        ['x > 10'],
        ['return'],
        [],
        ['print(x - 1)'],
        ['print(x)']
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[keys[1]])

    expected_edges_function = [
        [['x: int'], ['x > 10']],
        [['x > 10'], ['return']],
        [['return'], []],
        [['x > 10'], ['print(x - 1)']],
        [['print(x - 1)'], ['print(x)']],
        [['print(x)'], []]
    ]
    assert expected_edges_function == _extract_edges(cfgs[keys[1]])


def test_function_with_while_if_and_return() -> None:
    src = """
    def func(x: int) -> None:
        while x > 10:
            if x > 20:
                return
            print(x + 1)
        else:
            print(x - 1)
        print(x)
    """
    cfgs = build_cfgs(src)
    assert len(cfgs) == 2

    keys = list(cfgs)

    expected_blocks_module = [
        ['\ndef func(x: int) -> None:\n    while x > 10:\n        if x > 20:\n            '
         'return\n        print(x + 1)\n    else:\n        '
         'print(x - 1)\n    print(x)'],
        []
    ]
    assert expected_blocks_module == _extract_blocks(cfgs[keys[0]])

    expected_blocks_function = [
        ['x: int'],
        ['x > 10'],
        ['x > 20'],
        ['return'],
        [],
        ['print(x + 1)'],
        ['print(x - 1)'],
        ['print(x)']
    ]
    assert expected_blocks_function == _extract_blocks(cfgs[keys[1]])

    expected_edges_function = [
        [['x: int'], ['x > 10']],
        [['x > 10'], ['x > 20']],
        [['x > 20'], ['return']],
        [['return'], []],
        [['x > 20'], ['print(x + 1)']],
        [['print(x + 1)'], ['x > 10']],
        [['x > 10'], ['print(x - 1)']],
        [['print(x - 1)'], ['print(x)']],
        [['print(x)'], []]
    ]
    assert expected_edges_function == _extract_edges(cfgs[keys[1]])
