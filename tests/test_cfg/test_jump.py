from __future__ import annotations

from typing import Union

import astroid
from astroid import nodes

from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfgs(src: str) -> dict[Union[nodes.FunctionDef, nodes.Module], ControlFlowGraph]:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)
    return t.cfgs


def _extract_blocks(cfg: ControlFlowGraph) -> list[list[str]]:
    return [[s.as_string() for s in block.statements] for block in cfg.get_blocks()]


def test_link_break_to_block() -> None:
    src = """
    while x > 10:
        break
    """
    cfgs = build_cfgs(src)
    keys = list(cfgs)
    cfg = cfgs[keys[0]]

    break_block = cfg.start.successors[0].target
    assert break_block.statements[0].as_string() == "break"

    new_block = cfg.create_block(break_block)
    assert new_block.predecessors == []


def test_link_continue_to_block() -> None:
    src = """
    while x > 10:
        continue
    """
    cfgs = build_cfgs(src)
    keys = list(cfgs)
    cfg = cfgs[keys[0]]

    cont_block = cfg.start.successors[0].target
    assert cont_block.statements[0].as_string() == "continue"

    new_block = cfg.create_block(cont_block)
    assert new_block.predecessors == []


def test_link_return_to_block() -> None:
    src = """
    def func():
        return
    """
    cfgs = build_cfgs(src)
    keys = list(cfgs)
    cfg = cfgs[keys[1]]

    return_block = cfg.start.successors[0].target
    assert return_block.statements[0].as_string() == "return"

    new_block = cfg.create_block(return_block)
    assert new_block.predecessors == []


def test_link_raise_to_block() -> None:
    src = """
    def func():
        raise NotImplementedError
    """
    cfgs = build_cfgs(src)
    keys = list(cfgs)
    cfg = cfgs[keys[1]]

    raise_block = cfg.start.successors[0].target
    assert raise_block.statements[0].as_string() == "raise NotImplementedError"

    new_block = cfg.create_block(raise_block)
    assert new_block.predecessors == []
