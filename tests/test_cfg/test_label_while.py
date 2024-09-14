from __future__ import annotations

import astroid

from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> ControlFlowGraph:
    """Build a CFG for testing."""
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)

    return t.cfgs[mod]


def _extract_labels(cfg: ControlFlowGraph) -> set[str]:
    """Return a set of all the labels in this cfg."""
    labels = {edge.get_label() for edge in cfg.get_edges() if edge.get_label() is not None}
    return labels


def _extract_num_labels(cfg: ControlFlowGraph) -> int:
    """Return the number of labelled edges in the cfg."""
    return sum(1 for edge in cfg.get_edges() if edge.get_label() is not None)


def _extract_edge_conditions(cfg: ControlFlowGraph) -> list[str]:
    """Return the edge conditions in the given cfg as a list of strings representing the condition."""

    conditions = [
        edge.condition.as_string() for edge in cfg.get_edges() if edge.condition is not None
    ]
    return conditions


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


def test_while_conditions() -> None:
    """Test that the conditions are correctly set for edges produced in a while loop."""
    src = """
    i = 0
    while i < 10:
        i += 1

    print('not else')
    """
    expected_num_conditions = 2
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "i < 10" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_while_else_conditions() -> None:
    """Test that the conditions are correctly set for edges produced in a while-else loop."""
    src = """
    i = 0
    while i < 10:
        i += 1
    else:
        print('is else')

    print('not else')
    """
    expected_num_conditions = 2
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "i < 10" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_complex_while_conditions() -> None:
    """Test that the conditions are correctly set for edges produced in a complex while loop."""
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
    expected_num_conditions = 6
    found_conditions = _extract_edge_conditions(build_cfg(src))
    expected_conditions = ["i < 10", "j < 5", "j < 5", "i > 4", "i > 4", "i < 10"]
    assert found_conditions == expected_conditions
    assert len(found_conditions) == expected_num_conditions


def test_complex_while_else_conditions() -> None:
    """Test that the conditions are correctly set for edges produced in a complex while-else loop."""
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
    expected_num_conditions = 6
    found_conditions = _extract_edge_conditions(build_cfg(src))
    expected_conditions = ["i < 10", "j < 5", "j < 5", "i > 4", "i > 4", "i < 10"]
    assert found_conditions == expected_conditions
    assert len(found_conditions) == expected_num_conditions
