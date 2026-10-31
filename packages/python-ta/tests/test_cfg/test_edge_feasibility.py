from unittest.mock import patch

import astroid
from astroid import nodes
from python_ta_z3 import Z3Visitor

from python_ta.cfg import CFGVisitor, ControlFlowGraph


def test_unfeasible_simple_function() -> None:
    src = """
    def func(x: str) -> None:
        '''
        Preconditions:
            - x[0] == "a"
            - x[0:2] == "bc"
        '''
        print(x)
    """
    cfg = _create_cfg(src, "func")
    assert all(not edge.is_feasible for edge in cfg.get_edges())


def test_unfeasible_if_condition() -> None:
    src = """
    def func(x: int) -> None:
        '''
        Preconditions:
            - x > 0
        '''
        if x < 0:
            print("unreachable")
        print("end")
    """
    cfg = _create_cfg(src, "func")
    expected_if_path = [True, False, False, True]
    expected_other_path = [True, True, True]

    paths = cfg.get_paths()
    assert all(edge.is_feasible == expected for edge, expected in zip(paths[0], expected_if_path))
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_other_path)
    )


def test_unfeasible_if_else() -> None:
    src = """
    def func(x: str, y: int) -> None:
        '''
        Preconditions:
            - x[0] == "a"
            - y > 5
        '''
        print(x[0])
        if x[0] == "b":
            print(x)
        elif y < 0:
            print(y)
        else:
            print("pass")
        print("end")
        """
    cfg = _create_cfg(src, "func")
    expected_if_path = [True, False, False, True]
    expected_elif_path = [True, True, False, False, True]
    expected_else_path = [True, True, True, True, True]

    paths = cfg.get_paths()
    assert all(edge.is_feasible == expected for edge, expected in zip(paths[0], expected_if_path))
    assert all(edge.is_feasible == expected for edge, expected in zip(paths[1], expected_elif_path))
    assert all(edge.is_feasible == expected for edge, expected in zip(paths[2], expected_else_path))


def test_unfeasible_while_condition() -> None:
    src = """
    def func(x: int, y: int) -> None:
        '''
        Preconditions:
            - x > 10
            - y > 10
        '''
        while x + y < 15:
            print("unreachable")
        print("end")
    """
    cfg = _create_cfg(src, "func")
    expected_while_path = [True, False, False]
    expected_other_path = [True, True, True]

    paths = cfg.get_paths()
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[0], expected_while_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_other_path)
    )


def test_unfeasible_while_condition_with_reassignment() -> None:
    src = """
    def func(x: int, y: int) -> None:
        '''
        Preconditions:
            - x > 10
            - y > 10
        '''
        while x + y < 15:
            print("unreachable")
            x -= 1
            y -= 1
        print("end")
    """
    cfg = _create_cfg(src, "func")
    expected_while_path = [True, False, True]
    expected_other_path = [True, True, True]

    paths = cfg.get_paths()
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[0], expected_while_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_other_path)
    )


def test_unfeasible_nested_if() -> None:
    src = """
    def func(x: float, y: float) -> None:
        '''
        Preconditions:
            - x < 0
            - y < 0
        '''
        if x > 10:
            print(x)
            if y < -10:
                print(y)
        print("end")
    """
    cfg = _create_cfg(src, "func")
    expected_inner_path = [True, False, False, False, True]
    expected_outer_path = [True, False, False, True]
    expected_other_path = [True, True, True]

    paths = cfg.get_paths()
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[0], expected_inner_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_outer_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[2], expected_other_path)
    )


def test_unfeasible_nested_inner_if() -> None:
    src = """
    def func(x: float, y: float) -> None:
        '''
        Preconditions:
            - x < 0
            - y < 0
        '''
        if x < 10:
            print(x)
            if y > 0:
                print(y)
        print("end")
    """
    cfg = _create_cfg(src, "func")
    expected_inner_path = [True, True, False, False, True]
    expected_outer_path = [True, True, True, True]
    expected_other_path = [True, False, True]

    paths = cfg.get_paths()
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[0], expected_inner_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_outer_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[2], expected_other_path)
    )


def test_feasible_simple_function() -> None:
    src = """
    def func(x: str) -> None:
        '''
        Preconditions:
            - x in {"aaa", "aab", "bcd"}
            - x[0] == "a"
        '''
        print(x)
    """
    cfg = _create_cfg(src, "func")
    assert all(edge.is_feasible for edge in cfg.get_edges())


def test_feasible_no_precondition() -> None:
    src = """
    def func(x: int) -> None:
        print(x)
        if x > 5:
            print("x greater than 5")
        print("end")
    """
    cfg = _create_cfg(src, "func")
    assert all(edge.is_feasible for edge in cfg.get_edges())


def test_feasible_if_condition() -> None:
    src = """
    def func(x: float) -> None:
        '''
        Preconditions:
            - x > 10
        '''
        if x >= 10:
            print("inside if")
        print("end")
    """
    cfg = _create_cfg(src, "func")
    expected_if_path = [True, True, True, True]
    expected_other_path = [True, False, True]

    paths = cfg.get_paths()
    assert all(edge.is_feasible == expected for edge, expected in zip(paths[0], expected_if_path))
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_other_path)
    )


def test_feasible_while_condition() -> None:
    src = """
    def func(x: int, condition: bool) -> None:
        '''
        Preconditions:
            - condition
            - x in [1, 2, 3, 4, 5]
        '''
        while condition:
            print(x)
            if x > 3:
                break
        print("end")
    """
    cfg = _create_cfg(src, "func")
    expected_other_path = [True, False, True]

    paths = cfg.get_paths()
    assert all(edge.is_feasible for edge in paths[0])
    assert all(edge.is_feasible for edge in paths[1])
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[2], expected_other_path)
    )


def test_unfeasible_if_in_while() -> None:
    src = """
    def func(x: int) -> None:
        '''
        Preconditions:
            - x in (1, 2, 3, 4, 5)
        '''
        while x > 2:
            print(x)
            if x > 10:
                break
        print("end")
    """
    cfg = _create_cfg(src, "func")

    expected_break_path = [True, True, False, False, True]
    expected_not_break_path = [True, True, True]
    expected_other_path = [True, True, True]

    paths = cfg.get_paths()
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[0], expected_break_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_not_break_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[2], expected_other_path)
    )


def test_feasible_for_loop() -> None:
    src = """
    def func(x: str, y: int) -> None:
        '''
        Preconditions:
            - x[0] == "a"
            - y > 0
        '''
        for i in range(0, y):
             print(x)
        print("end")
    """
    cfg = _create_cfg(src, "func")
    assert all(edge.is_feasible for edge in cfg.get_edges())


def test_variable_reassignment() -> None:
    src = """
    def func(x: int) -> None:
        '''
        Preconditions:
            - x > 10
        '''
        if x < 10:
            print("unreachable")
        x = 5
        if x < 10:
            print("reachable")
    """
    cfg = _create_cfg(src, "func")
    expected_if_path1 = [True, False, False, True, True]
    expected_if_path2 = [True, False, False, True]
    expected_other_path1 = [True, True, True, True]
    expected_other_path2 = [True, True, True]

    paths = cfg.get_paths()
    assert all(edge.is_feasible == expected for edge, expected in zip(paths[0], expected_if_path1))
    assert all(edge.is_feasible == expected for edge, expected in zip(paths[1], expected_if_path2))
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[2], expected_other_path1)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[3], expected_other_path2)
    )


@patch.dict("sys.modules", {"z3": None})
def test_z3_dependency_uninstalled() -> None:
    src = """
    def func(x: str) -> None:
        '''
        Preconditions:
            - x[0] == "a"
            - x[0:2] == "bc"
        '''
        print(x)
    """
    visitor = CFGVisitor(z3_enabled=True)
    mod = astroid.parse(src)
    mod.accept(visitor)
    func_node = None
    for node in mod.body:
        if isinstance(node, nodes.FunctionDef) and node.name == "func":
            func_node = node
            break
    cfg = visitor.cfgs[func_node]

    assert all(edge.is_feasible for edge in cfg.get_edges())


def _create_cfg(src: str, name: str) -> ControlFlowGraph:
    """
    Return the control flow graph of given function
    generated from the source code
    """
    z3v = Z3Visitor()
    mod = z3v.visitor.visit(astroid.parse(src))
    visitor = CFGVisitor(z3_enabled=True)
    mod.accept(visitor)

    # find the function definition node
    func_node = None
    for node in mod.body:
        if isinstance(node, nodes.FunctionDef) and node.name == name:
            func_node = node
            break

    assert func_node is not None
    return visitor.cfgs[func_node]


@patch.dict("sys.modules", {"z3": None})
def test_update_edge_z3_import_fail() -> None:
    """Test verifies if `update_edge_z3_constraints` handles import errors as expected."""
    cfg = ControlFlowGraph(z3_enabled=True)
    assert cfg.update_edge_z3_constraints() is None


@patch.dict("sys.modules", {"z3": None})
def test_update_edge_feasibility_import_fail() -> None:
    """Test verifies if `update_edge_feasibility` handles import errors as expected."""
    cfg = ControlFlowGraph(z3_enabled=True)
    assert cfg.update_edge_feasibility() is None
