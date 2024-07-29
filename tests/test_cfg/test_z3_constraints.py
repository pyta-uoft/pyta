from typing import List

import astroid
import z3

from python_ta.cfg import CFGVisitor, ControlFlowGraph


def test_simple_function() -> None:
    src = """
    def func(x: int, y: int) -> int:
        '''
        Preconditions:
            - x > 0 and y > 0
            - x >= y
        '''
        print(x + y)
    """
    cfg = _create_cfg(src, "func")
    x = z3.Int("x")
    y = z3.Int("y")
    expected = [z3.And(x > 0, y > 0), x >= y]
    assert all(edge.z3_constraints == expected for edge in cfg.get_edges())


def test_if_statement() -> None:
    src = """
    def func(x: int, y: bool) -> None:
        '''
        Preconditions:
            - x > 0
        '''
        print("before if")
        if x > 5 and y:
            print("inside if")
        print("after if")
    """
    cfg = _create_cfg(src, "func")
    x = z3.Int("x")
    y = z3.Bool("y")
    expected_if_true = [x > 0, z3.And(x > 5, y)]
    expected_other = [x > 0]
    for edge in cfg.get_edges():
        if edge.label == "True":
            assert _list_equal(edge.z3_constraints, expected_if_true)
        else:
            assert _list_equal(edge.z3_constraints, expected_other)


def test_if_else() -> None:
    src = """
    def func(x: str, y: int) -> None:
        '''
        Preconditions:
            - x[0] == "a"
            - y > 5
        '''
        print(x[0])
        if x == "abc":
            print(x)
        elif y > 10:
            print(y)
        else:
            print("pass")
        print("end")
    """
    cfg = _create_cfg(src, "func")
    x = z3.String("x")
    y = z3.Int("y")

    expected_constraints = [[x == "abc"], [y > 10]]

    # recursively traverse through if branches and check constraints
    def assert_constraints(node, previous_constraints, index):
        for edge in node.successors:
            if edge.label == "True":
                new_constraints = previous_constraints + expected_constraints[index]
                assert _list_equal(edge.z3_constraints, new_constraints)
            elif edge.label == "False":
                new_constraints = previous_constraints + [z3.Not(*(expected_constraints[index]))]
                assert _list_equal(edge.z3_constraints, new_constraints)
                assert_constraints(edge.target, new_constraints, index + 1)

    start_edge = cfg.start.successors[0]
    assert _list_equal(start_edge.z3_constraints, [z3.SubString(x, 0, 1) == "a", y > 5])
    assert_constraints(start_edge.target, [z3.SubString(x, 0, 1) == "a", y > 5], 0)
    assert _list_equal(
        cfg.end.predecessors[0].z3_constraints, [z3.SubString(x, 0, 1) == "a", y > 5]
    )


def test_variable_reassignment() -> None:
    src = """
    def func(x: float) -> None:
        '''
        Preconditions:
            - x in [1.0, 2.0, 3.0]
        '''
        print("initial x:", x)
        x = "x"
        print("final x:", x)
    """
    cfg = _create_cfg(src, "func")
    x = z3.Real("x")
    assert _list_equal(
        cfg.start.successors[0].z3_constraints, [z3.Or(x == 1.0, x == 2.0, x == 3.0)]
    )
    assert cfg.end.predecessors[0].z3_constraints == []


def test_variable_reassignment_in_branch() -> None:
    src = """
    def func(x: float) -> None:
        '''
        Preconditions:
            - x in [1.0, 2.0, 3.0]
        '''
        print("initial x:", x)
        if x < 5:
            x = 10
            print("x in if block:", x)
        print("final x:", x)
    """


def test_variable_shadowing() -> None:
    src = """
    def outer(x: int) -> None:
        '''
        Preconditions:
            - x > 10
        '''
        def inner():
            x = 5
        print(x)
    """
    cfg = _create_cfg(src, "outer")
    x = z3.Int("x")
    assert _list_equal(cfg.start.successors[0].z3_constraints, [x > 10])


def test_ignored_precondition() -> None:
    src = """
    def func(x: int) -> None:
        '''
        Preconditions:
            - x > 5
            - a > 5
        '''
        print(x)
    """
    cfg = _create_cfg(src, "func")
    x = z3.Int("x")
    expected = [x > 5]
    assert all(edge.z3_constraints == expected for edge in cfg.get_edges())


def test_ignored_if_condition() -> None:
    src = """
        def func(x: int) -> None:
            '''
            Preconditions:
                - x > 5
            '''
            a = 10
            if a > 5:
                print(a)
            else:
                print(x)
        """
    cfg = _create_cfg(src, "func")
    x = z3.Int("x")
    expected = [x > 5]
    assert all(edge.z3_constraints == expected for edge in cfg.get_edges())


def _create_cfg(src: str, name: str) -> ControlFlowGraph:
    """
    Return the control flow graph of given function
    generated from the source code
    """
    mod = astroid.parse(src)
    visitor = CFGVisitor()
    mod.accept(visitor)

    # find the function definition node
    func_node = None
    for node in mod.body:
        if isinstance(node, astroid.FunctionDef) and node.name == name:
            func_node = node
            break

    assert func_node is not None
    return visitor.cfgs[func_node]


def _list_equal(lst1: List, lst2: List) -> bool:
    """
    A more efficient way to determine whether two lists contain
    the same elements, regardless of orders
    """
    return set(lst1) == set(lst2)
