from typing import List
import astroid
from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> ControlFlowGraph:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)

    return t.cfgs[mod]


def _extract_blocks(cfg: ControlFlowGraph) -> List[List[str]]:
    """Block extraction for boolean 'and' expressions visits the `false`
    block first. While for boolean 'or' expressions, the 'true' block is visited
    first."""
    return [
        [s.as_string() for s in block.statements]
        for block in cfg.get_blocks()
    ]


def _extract_edges(cfg: ControlFlowGraph) -> List[List[List[str]]]:
    """Edge extraction for boolean 'and' expressions visits the `false`
    edge first. While for boolean 'or' expressions, the 'true' edge is visited
    first."""
    edges = [[edge.source.statements, edge.target.statements] for edge in cfg.get_edges()]
    expanded_edges = [[[source.as_string() for source in edge[0]],
                      [target.as_string() for target in edge[1]]]
                      for edge in edges]
    return expanded_edges


"""
Notes:
    - Tests for `if` and `while` are exactly the same. There should not be any
      difference between the CFG of a boolean expression in an `if` condition or
      a `while` condition.
"""


def test_if_simple_or() -> None:
    src = """
    if x or y:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_then'],
        [],
        ['y'],
        ['_else']
    ]
    assert expected_blocks == _extract_blocks(cfg)


def test_if_simple_and() -> None:
    src = """
    if x and y:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_else'],
        [],
        ['y'],
        ['_then'],
    ]
    assert expected_blocks == _extract_blocks(cfg)


def test_if_multiple_or() -> None:
    src = """
    if x or y or z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_then'],
        [],
        ['y'],
        ['z'],
        ['_else']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_then']],
        [['_then'], []],
        [['x'], ['y']],
        [['y'], ['_then']],
        [['y'], ['z']],
        [['z'], ['_then']],
        [['z'], ['_else']],
        [['_else'], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_if_multiple_and() -> None:
    src = """
    if x and y and z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_else'],
        [],
        ['y'],
        ['z'],
        ['_then'],
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_else']],
        [['_else'], []],
        [['x'], ['y']],
        [['y'], ['_else']],
        [['y'], ['z']],
        [['z'], ['_else']],
        [['z'], ['_then']],
        [['_then'], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_if_simple_or_with_and() -> None:
    src = """
    if x or y and z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_then'],
        [],
        ['y'],
        ['_else'],
        ['z']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_then']],
        [['_then'], []],
        [['x'], ['y']],
        [['y'], ['_else']],
        [['_else'], []],
        [['y'], ['z']],
        [['z'], ['_else']],
        [['z'], ['_then']]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_if_simple_or_with_and_swapped_operands() -> None:
    src = """
        if x and y or z:
            _then
        else:
            _else
        """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['z'],
        ['_then'],
        [],
        ['_else'],
        ['y']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['z']],
        [['z'], ['_then']],
        [['_then'], []],
        [['z'], ['_else']],
        [['_else'], []],
        [['x'], ['y']],
        [['y'], ['z']],
        [['y'], ['_then']]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_if_simple_and_with_or() -> None:
    src = """
    if x and (y or z):
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_else'],
        [],
        ['y'],
        ['_then'],
        ['z']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_else']],
        [['_else'], []],
        [['x'], ['y']],
        [['y'], ['_then']],
        [['_then'], []],
        [['y'], ['z']],
        [['z'], ['_then']],
        [['z'], ['_else']]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_if_simple_and_with_or_swapped_operands() -> None:
    src = """
    if (x or y) and z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['z'],
        ['_else'],
        [],
        ['_then'],
        ['y']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['z']],
        [['z'], ['_else']],
        [['_else'], []],
        [['z'], ['_then']],
        [['_then'], []],
        [['x'], ['y']],
        [['y'], ['z']],
        [['y'], ['_else']],
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_simple_or() -> None:
    src = """
    while x or y:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_then'],
        [],
        ['y'],
        ['_else']
    ]
    assert expected_blocks == _extract_blocks(cfg)


def test_while_simple_and() -> None:
    src = """
    while x and y:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_else'],
        [],
        ['y'],
        ['_then'],
    ]
    assert expected_blocks == _extract_blocks(cfg)


def test_while_multiple_or() -> None:
    src = """
    while x or y or z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_then'],
        [],
        ['y'],
        ['z'],
        ['_else']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_then']],
        [['_then'], []],
        [['x'], ['y']],
        [['y'], ['_then']],
        [['y'], ['z']],
        [['z'], ['_then']],
        [['z'], ['_else']],
        [['_else'], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_multiple_and() -> None:
    src = """
    while x and y and z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_else'],
        [],
        ['y'],
        ['z'],
        ['_then'],
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_else']],
        [['_else'], []],
        [['x'], ['y']],
        [['y'], ['_else']],
        [['y'], ['z']],
        [['z'], ['_else']],
        [['z'], ['_then']],
        [['_then'], []]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_simple_or_with_and() -> None:
    src = """
    while x or y and z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_then'],
        [],
        ['y'],
        ['_else'],
        ['z']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_then']],
        [['_then'], []],
        [['x'], ['y']],
        [['y'], ['_else']],
        [['_else'], []],
        [['y'], ['z']],
        [['z'], ['_else']],
        [['z'], ['_then']]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_simple_or_with_and_swapped_operands() -> None:
    src = """
        while x and y or z:
            _then
        else:
            _else
        """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['z'],
        ['_then'],
        [],
        ['_else'],
        ['y']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['z']],
        [['z'], ['_then']],
        [['_then'], []],
        [['z'], ['_else']],
        [['_else'], []],
        [['x'], ['y']],
        [['y'], ['z']],
        [['y'], ['_then']]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_simple_and_with_or() -> None:
    src = """
    while x and (y or z):
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['_else'],
        [],
        ['y'],
        ['_then'],
        ['z']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['_else']],
        [['_else'], []],
        [['x'], ['y']],
        [['y'], ['_then']],
        [['_then'], []],
        [['y'], ['z']],
        [['z'], ['_then']],
        [['z'], ['_else']]
    ]
    assert expected_edges == _extract_edges(cfg)


def test_while_simple_and_with_or_swapped_operands() -> None:
    src = """
    while (x or y) and z:
        _then
    else:
        _else
    """
    cfg = build_cfg(src)

    expected_blocks = [
        ['x'],
        ['z'],
        ['_else'],
        [],
        ['_then'],
        ['y']
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [['x'], ['z']],
        [['z'], ['_else']],
        [['_else'], []],
        [['z'], ['_then']],
        [['_then'], []],
        [['x'], ['y']],
        [['y'], ['z']],
        [['y'], ['_else']],
    ]
    assert expected_edges == _extract_edges(cfg)
