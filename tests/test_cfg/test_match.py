from __future__ import annotations

import sys

import astroid
import pytest

from python_ta.cfg import CFGVisitor, ControlFlowGraph

if sys.version_info < (3, 10):
    pytest.skip("match statements are not supported in Python < 3.10", allow_module_level=True)


def build_cfg(src: str) -> ControlFlowGraph:
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)

    return t.cfgs[mod]


def _extract_blocks(cfg: ControlFlowGraph) -> list[list[str]]:
    return [[s.as_string() for s in block.statements] for block in cfg.get_blocks()]


def test_simple_match() -> None:
    """Assert that a simple match statement is parsed correctly"""
    src = """
    match x:
        case 1:
            print('one')
        case 2:
            print('two')
    """
    expected_blocks = [["x"], ["print('one')"], [], ["print('two')"]]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_match_with_multiple_statements() -> None:
    """Assert that a match statement with multiple statements in each case is parsed correctly"""
    src = """
    match x:
        case 1:
            print('one')
            print('still one')
        case 2:
            print('two')
            print('still two')
    """
    expected_blocks = [
        ["x"],
        ["print('one')", "print('still one')"],
        [],
        ["print('two')", "print('still two')"],
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_match_with_gaurds() -> None:
    """Assert that a match statement with guards is parsed correctly"""
    src = """
    match x:
        case 1 if x > 0:
            print('one')
        case 2 if x < 0:
            print('two')
    """
    expected_blocks = [["x"], ["x > 0", "print('one')"], [], ["x < 0", "print('two')"]]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_match_surrounding_statements() -> None:
    """Assert that a match statement with surrounding statements is parsed correctly"""
    src = """
    print('before match')
    match x:
        case 1:
            print('one')
        case 2:
            print('two')
    print('after match')
    """
    expected_blocks = [
        ["print('before match')", "x"],
        ["print('one')"],
        ["print('after match')"],
        [],
        ["print('two')"],
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks


def test_nested_match() -> None:
    """Assert that a nested match statement is parsed correctly"""
    src = """
    match x:
        case 1:
            print('one')
            match y:
                case 2:
                    print('nested two')
                case _:
                    print('nested default')
        case 3:
            print('three')
    """
    expected_blocks = [
        ["x"],
        ["print('one')", "y"],
        ["print('nested two')"],
        [],
        ["print('nested default')"],
        ["print('three')"],
    ]
    assert _extract_blocks(build_cfg(src)) == expected_blocks
