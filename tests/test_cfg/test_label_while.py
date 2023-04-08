from typing import Set

import astroid

from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> ControlFlowGraph:
    """Build a CFG for testing."""
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)

    return t.cfgs[mod]


def _extract_labels(cfg: ControlFlowGraph) -> Set[str]:
    """Return a set of all the labels in this cfg."""
    labels = {edge.label for edge in cfg.get_edges() if edge.label is not None}
    return labels


def _extract_num_labels(cfg: ControlFlowGraph) -> int:
    """Return the number of labelled edges in the cfg."""
    return sum(1 for edge in cfg.get_edges() if edge.label is not None)


def test_num_while_labels() -> None:
    """Test that the expected number of labels is produced in a while loop."""
    src = """
    i = 0
    while i < 10:
        i += 1

    print('not else')
    """
    expected_num_labels = 2
    assert _extract_num_labels(build_cfg(src)) == expected_num_labels


def test_type_while_labels() -> None:
    """Test that the content of the labels produced in a while loop is correct."""
    src = """
    i = 0
    while i < 10:
        i += 1

    print('not else')
    """
    expected_labels = {"True", "False"}
    assert _extract_labels(build_cfg(src)) == expected_labels


def test_num_while_else_labels() -> None:
    """Test that the expected number of labels is produced in a while-else loop."""
    src = """
    i = 0
    while i < 10:
        i += 1
    else:
        print('is else')

    print('not else')
    """
    expected_num_labels = 2
    assert _extract_num_labels(build_cfg(src)) == expected_num_labels


def test_type_while_else_labels() -> None:
    """Test that the content of the labels produced in a while-else loop is correct."""
    src = """
    i = 0
    while i < 10:
        i += 1
    else:
        print('is else')

    print('not else')
    """
    expected_labels = {"True", "False"}
    assert _extract_labels(build_cfg(src)) == expected_labels


def test_num_complex_while_labels() -> None:
    """Test that the number of labels in a complex while loop is correct."""
    src = """
    i = 0
    while i < 10:
        j = 0
        while j < 5:
            j += 1
        i += 1

        if i > 4:
            print('hi')

    print('not else')
    """
    expected_num_labels = 6
    assert _extract_num_labels(build_cfg(src)) == expected_num_labels


def test_type_complex_while_labels() -> None:
    """Test that the content of the labels produced in a complex while loop is correct."""
    src = """
    i = 0
    while i < 10:
        j = 0
        while j < 5:
            j += 1
        i += 1

        if i > 4:
            print('hi')

    print('not else')
    """
    expected_labels = {"True", "False"}
    assert _extract_labels(build_cfg(src)) == expected_labels


def test_num_complex_while_else_labels() -> None:
    """Test that the number of labels in a complex while-else loop is correct."""
    src = """
    i = 0
    while i < 10:
        j = 0
        while j < 5:
            j += 1
        i += 1

        if i > 4:
            print('hi')
    else:
        print('is else')

    print('not else')
    """
    expected_num_labels = 6
    assert _extract_num_labels(build_cfg(src)) == expected_num_labels


def test_type_complex_while_else_labels() -> None:
    """Test that the content of the labels produced in a complex while-else loop is correct."""
    src = """
    i = 0
    while i < 10:
        j = 0
        while j < 5:
            j += 1
        i += 1

        if i > 4:
            print('hi')
    else:
        print('is else')

    print('not else')
    """
    expected_labels = {"True", "False"}
    assert _extract_labels(build_cfg(src)) == expected_labels
