import astroid
import z3

from python_ta.cfg import CFGVisitor, ControlFlowGraph
from python_ta.transforms.z3_visitor import Z3Visitor


def test_unfeasible_if_condition() -> None:
    src = """
    def func(x: int) -> int:
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


def test_unfeasible_while_condition() -> None:
    src = """
    def func(x: int, y: int) -> int:
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
    expected_while_path = [True, False]
    expected_other_path = [True, True, True]

    paths = cfg.get_paths()
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[0], expected_while_path)
    )
    assert all(
        edge.is_feasible == expected for edge, expected in zip(paths[1], expected_other_path)
    )


def test_feasible_break_in_while() -> None:
    src = """
    def func(x: int, y: int, condition: bool) -> None:
        '''
        Preconditions:
            - x > y
            - condition
        '''
        while condition:
            if x < y:
                break
            y += 1
        print("break")
    """
    cfg = _create_cfg(src, "func")
    assert all(edge.is_feasible for edge in cfg.get_edges())


def _create_cfg(src: str, name: str) -> ControlFlowGraph:
    """
    Return the control flow graph of given function
    generated from the source code
    """
    z3v = Z3Visitor()
    mod = z3v.visitor.visit(astroid.parse(src))
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
