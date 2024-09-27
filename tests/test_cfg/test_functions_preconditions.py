from __future__ import annotations

import astroid

from python_ta.cfg import CFGVisitor, ControlFlowGraph


def build_cfg(src: str) -> list[ControlFlowGraph]:
    """Build a CFG for testing and return all CFGs built."""
    mod = astroid.parse(src)
    t = CFGVisitor()
    mod.accept(t)
    return list(t.cfgs.values())


def _extract_edge_conditions(cfgs: list[ControlFlowGraph]) -> list[str]:
    """Return the edge conditions in the given list of cfgs as a list of strings representing the condition."""
    conditions = [
        edge.condition.as_string()
        for cfg in cfgs
        for edge in cfg.get_edges()
        if edge.condition is not None
    ]
    return conditions


def test_condition_no_preconditions() -> None:
    """Test that the condition node in a function CFG is not created if there are no preconditions."""
    src = """
    def func(x: int) -> None:
        print(x + 1)
    """
    expected_num_conditions = 0
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert len(found_conditions) == expected_num_conditions


def test_condition_one_precondition() -> None:
    """Test that the condition node in a function CFG is created properly if there is a precondition."""
    src = """def divide(x: int, y: int) -> int:
        \"\"\"Return x // y.
        Preconditions:
           - y != 0
        \"\"\"
        return x // y
    """
    expected_num_conditions = 1
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "y != 0" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_condition_one_precondition_with_surrounding_statements() -> None:
    """Test that the condition node in a function CFG is created properly if there is a precondition and
    surrounding statements."""
    src = """
    x = 10
    def divide(x: int, y: int) -> int:
        \"\"\"Return x // y.
        Preconditions:
           - y != 0
        \"\"\"
        return x // y
    print(x)
    """
    expected_num_conditions = 1
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "y != 0" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_condition_invalid_precondition() -> None:
    """Test that the condition node in a function CFG is not created for an invalid Python precondition."""
    src = """def divide(x: int, y: int) -> int:
        \"\"\"Return x // y.
        Preconditions:
           - bad precondition
        \"\"\"
        return x // y
    """
    expected_num_conditions = 0
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert len(found_conditions) == expected_num_conditions


def test_condition_one_precondition_multiple_functions() -> None:
    """Test that the condition node in a function CFG is created properly if there is a precondition in
    multiple functions."""
    src = """
    def divide(x: int, y: int) -> int:
        \"\"\"Return x // y.
        Preconditions:
           - y != 0
        \"\"\"
        return x // y

    def multiply(a: int, b: int) -> int:
        \"\"\"Return a * b.
        Preconditions:
           - b > 0
        \"\"\"
        return a * b
    """
    expected_num_conditions = 2
    found_conditions = _extract_edge_conditions(build_cfg(src))
    expected_conditions = ["y != 0", "b > 0"]
    assert found_conditions == expected_conditions
    assert len(found_conditions) == expected_num_conditions


def test_condition_multiple_preconditions() -> None:
    """Test that the condition node in a function CFG is created properly if there are multiple preconditions."""
    src = """def divide(x: int, y: int) -> int:
        \"\"\"Return x // y.
        Preconditions:
           - y != 0
           - x > 0
           - x + y < 100
        \"\"\"
        return x // y
    """
    expected_num_conditions = 1
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "y != 0 and x > 0 and x + y < 100" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_condition_invalid_precondition_multiple_preconditions() -> None:
    """Test that the condition node in a function CFG is not created for an invalid Python precondition with the
    but other preconditions are still created."""
    src = """def divide(x: int, y: int) -> int:
        \"\"\"Return x // y.
        Preconditions:
           - y != 0
           - bad precondition
        \"\"\"
        return x // y
    """
    expected_num_conditions = 1
    found_conditions = _extract_edge_conditions(build_cfg(src))
    assert all(condition == "y != 0" for condition in found_conditions)
    assert len(found_conditions) == expected_num_conditions


def test_condition_multiple_preconditions_multiple_functions() -> None:
    """Test that the condition node in a function CFG is created properly if there are multiple preconditions in
    multiple functions."""
    src = """
    def divide(x: int, y: int) -> int:
        \"\"\"Return x // y.
        Preconditions:
           - y != 0
           - x > 0
           - x + y < 100
        \"\"\"
        return x // y

    def multiply(a: int, b: int) -> int:
        \"\"\"Return a * b.
        Preconditions:
           - b > 0
           - a > 0
           - a + b != 100
        \"\"\"
        return a * b
    """
    expected_num_conditions = 2
    found_conditions = _extract_edge_conditions(build_cfg(src))
    expected_conditions = ["y != 0 and x > 0 and x + y < 100", "b > 0 and a > 0 and a + b != 100"]
    assert found_conditions == expected_conditions
    assert len(found_conditions) == expected_num_conditions
