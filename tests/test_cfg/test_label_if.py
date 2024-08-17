from typing import List, Tuple

import astroid

from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> ControlFlowGraph:
    """Build a CFG for testing."""
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)

    return t.cfgs[mod]


def _extract_edge_labels(cfg: ControlFlowGraph) -> Tuple[int, int]:
    """Return the number of True/False edge labels in the given cfg.

    The returned 2-tuple is of the form (# of True, # of False).
    """
    labels = [edge.get_label() for edge in cfg.get_edges()]
    return labels.count("True"), labels.count("False")


def _extract_edge_conditions(cfg: ControlFlowGraph) -> List[str]:
    """Return the edge conditions in the given cfg as a list of strings representing the condition."""

    conditions = [
        edge.condition.as_string() for edge in cfg.get_edges() if edge.condition is not None
    ]
    return conditions


def test_label_if_no_else() -> None:
    """Test that the labels from the if condition were correctly updated for an if block with no
    else statement."""
    src = """
    x = 0
    if x > 0:
        x = 4
    """
    expected_false_labels = 1
    expected_true_labels = 1
    assert _extract_edge_labels(build_cfg(src)) == (expected_true_labels, expected_false_labels)


def test_label_if_else() -> None:
    """Test that the labels from the if condition were correctly updated for an if block with an
    else statement."""
    src = """
    x = 0
    if x > 0:
        x = 4
    else:
        x = -1
    """
    expected_false_labels = 1
    expected_true_labels = 1
    assert _extract_edge_labels(build_cfg(src)) == (expected_true_labels, expected_false_labels)


def test_label_if_elsif() -> None:
    """Test that the labels from the if condition were correctly updated for an if block with
    elsif statements."""
    src = """
    x = 0
    if x > 5:
        x = 6
    elif x > 3:
        x = 4
    elif x > 0:
        x = 1
    else:
        x = -1
    """
    expected_false_labels = 3
    expected_true_labels = 3
    assert _extract_edge_labels(build_cfg(src)) == (expected_true_labels, expected_false_labels)


def test_condition_if_no_else() -> None:
    """Test that the condition nodes from the if condition were correctly updated for an if block with no
    else statement."""
    src = """
    x = 0
    if x > 0:
        x = 4
    """
    expected_num_conditions = 2
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "x > 0" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_condition_if_else() -> None:
    """Test that the condition nodes from the if condition were correctly updated for an if block with an
    else statement."""
    src = """
    x = 0
    if x > 0:
        x = 4
    else:
        x = -1
    """
    expected_num_conditions = 2
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "x > 0" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_condition_if_elsif() -> None:
    """Test that the condition nodes from the if condition were correctly updated for an if block with
    elsif statements."""
    src = """
    x = 0
    if x > 5:
        x = 6
    elif x > 3:
        x = 4
    elif x > 0:
        x = 1
    else:
        x = -1
    """
    expected_num_conditions = 6
    found_conditions = _extract_edge_conditions(build_cfg(src))
    expected_conditions = ["x > 5", "x > 5", "x > 3", "x > 3", "x > 0", "x > 0"]
    assert found_conditions == expected_conditions
    assert len(found_conditions) == expected_num_conditions
