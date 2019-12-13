from typing import List, Tuple
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


def _extract_edges(cfg: ControlFlowGraph) -> List[List[List[str]]]:
    edges = [[edge.source.statements, edge.target.statements] for edge in cfg.get_edges()]
    expanded_edges = [[[source.as_string() for source in edge[0]],
                      [target.as_string() for target in edge[1]]]
                      for edge in edges]
    return expanded_edges


def test_simple_with() -> None:
    src = """
    with open('file') as f:
        print(1)
        print(2)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["open('file')", "f", "print(1)", "print(2)"],
        []  # end block
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["open('file')", "f", "print(1)", "print(2)"], []]
    ]
    assert expected_edges == _extract_edges(cfg)

def test_with_for() -> None:
    src = """
    with open('file') as f:
        for i in range(10):
            print(i)
    """
    cfg = build_cfg(src)
    expected_blocks = [
        ["open('file')", "f", "range(10)"],
        ["i"],
        ["print(i)"],
        []  # end block
    ]
    assert expected_blocks == _extract_blocks(cfg)

    expected_edges = [
        [["open('file')", "f", "range(10)"], ["i"]],
        [["i"], ["print(i)"]],
        [["print(i)"], ["i"]],
        [["i"], []]
    ]
    assert expected_edges == _extract_edges(cfg)
