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
        ['except Exception:\n    pass', 'pass'],
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
        ['except Exception:\n    pass', 'pass'],
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
        ['except Exception:\n    pass', 'pass'],
        [],  # end block
        ['except KeyError as k:\n    pass', 'pass'],
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
        ['except Exception:\n    pass', 'pass'],
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
        ['except KeyError:\n    pass', 'pass'],
        ['except Exception:\n    pass', 'pass'],
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
        ['except KeyError:\n    pass', 'pass'],
        ['except Exception:\n    if x > 10:\n        '
         'print(True)\n    else:\n        print(False)', 'x > 10'],
        ['print(True)'],
        ['print(\'after\')'],
        [],  # end block
        ['print(False)'],
        ['x = 15'],
        ['except KeyError:\n    pass', 'pass'],
    ]
    ext = _extract_blocks(build_cfg(src))
    print(ext)
    assert ext == expected_blocks
