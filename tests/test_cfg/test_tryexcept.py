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


def test_simple() -> None:
    src = """
    try:
        print(True)
    except Exception:
        pass
    """
    expected_blocks = [
        ['print(True)'],
        ['pass'],
        []  # end block
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks

def test_named_exception() -> None:
    src = """
    try:
        print(True)
    except Exception as e:
        pass
    """
    expected_blocks = [
        ['print(True)'],
        ['e', 'pass'],
        []  # end block
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks



def test_before_after() -> None:
    src = """
        x = 0
        try:
            print(x)
        except Exception:
            pass
        print('after')
        """
    expected_blocks = [
        ['x = 0'],
        ['print(x)'],
        ['pass'],
        ['print(\'after\')'],
        []  # end block
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_multiple_exceptions() -> None:
    src = """
    try:
        print(True)
    except Exception:
        pass
    except KeyError as k:
        pass
    else:
        print('else')
    """
    expected_blocks = [
        ['print(True)'],
        ['pass'],
        [],  # end block
        ['k', 'pass'],
        ['print(\'else\')']
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_compound_statement() -> None:
    src = """
    try:
        x = 0
        if x > 10:
            print(x)
        else:
            print(x - 1)
    except Exception:
        pass
    """
    expected_blocks = [
        ['x = 0', 'x > 10'],
        ['print(x)'],
        ['pass'],
        [],  # end block
        ['print(x - 1)']
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_nested() -> None:
    src = """
    try:
        x = 0
        try:
            x = 10
        except KeyError:
            pass
    except Exception:
        pass
    """
    expected_blocks = [
        ['x = 0'],
        ['x = 10'],
        ['pass'],
        ['pass'],
        [],  # end block
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_complex() -> None:
    src = """
    x = 10
    try:
        try:
            while x > 5:
                x -= 1
        except KeyError:
            pass
    except Exception:
        if x > 10:
            print(True)
        else:
            print(False)
    else:
        try:
            x = 15
        except KeyError:
            pass
    print('after')
    """
    expected_blocks = [
        ['x = 10'],
        ['x > 5'],
        ['x -= 1'],
        ['pass'],
        ['x > 10'],
        ['print(True)'],
        ['print(\'after\')'],
        [],  # end block
        ['print(False)'],
        ['x = 15'],
        ['pass'],
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks
