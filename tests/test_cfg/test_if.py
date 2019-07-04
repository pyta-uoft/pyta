from typing import List
import astroid
from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> ControlFlowGraph:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)

    return t.cfgs[mod]


def _extract_blocks(cfg: ControlFlowGraph) -> List[List[str]]:
    return [
        [s.as_string() for s in block.statements]
        for block in cfg.get_blocks()
    ]


def test_simple_if_no_else() -> None:
    src = """
    if 3 > 1:
        print('hi')
    """
    expected_blocks = [
        ['3 > 1'],
        ['print(\'hi\')'],
        []  # end block
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_simple_if_else() -> None:
    src = """
    if 3 > 1:
        print('hi')
    else:
        print('bye')
    """
    expected_blocks = [
        ['3 > 1'],
        ['print(\'hi\')'],
        [],
        ['print(\'bye\')']
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_simple_if_multiple_branches() -> None:
    src = """
    if 3 > 1:
        print('hi')
    elif 3 > 4:
        print('hello')
    elif True:
        print('goodbye')
    else:
        print('bye')
    """
    expected_blocks = [
        ['3 > 1'],
        ['print(\'hi\')'],
        [],
        ['3 > 4'],
        ['print(\'hello\')'],
        ['True'],
        ['print(\'goodbye\')'],
        ['print(\'bye\')']
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_if_multiple_statements_in_branches() -> None:
    """Test an if statement with multiple statements in each branch."""
    src = """
    if 3 > 1:
        print('hi')
        print('hi')
    else:
        print('bye')
        print('bye')
        print('bye')
    """
    expected_blocks = [
        ['3 > 1'],
        ['print(\'hi\')', 'print(\'hi\')'],
        [],
        ['print(\'bye\')', 'print(\'bye\')', 'print(\'bye\')']
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_if_surrounding_statements() -> None:
    """Test an if statement with other statements before and after it."""
    src = """
    x = 1
    if x > 1:
        print('hi')
    else:
        print('bye')
    print(x)
    """
    expected_blocks = [
        ['x = 1', 'x > 1'],
        ['print(\'hi\')'],
        ['print(x)'],
        [],
        ['print(\'bye\')']
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_nested_if() -> None:
    src = """
    x = 1
    if x > 1:
        print('hi')
        if x == 2:
            print('nested')
        else:
            print('not nested')
        print('done')
    else:
        print('bye')
    print(x)
    """
    expected_blocks = [
        ['x = 1', 'x > 1'],
        ['print(\'hi\')', 'x == 2'],
        ['print(\'nested\')'],
        ['print(\'done\')'],
        ['print(x)'],
        [],
        ['print(\'not nested\')'],
        ['print(\'bye\')']
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks
