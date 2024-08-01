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
    expected = {1: [z3.And(x > 0, y > 0), x >= y]}
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
    expected_if_path = [
        [x > 0],
        [x > 0, z3.And(x > 5, y)],
        [x > 0, z3.And(x > 5, y)],
        [x > 0, z3.And(x > 5, y)],
    ]
    expected_other_path = [
        [x > 0],
        [x > 0, z3.Not(z3.And(x > 5, y))],
        [x > 0, z3.Not(z3.And(x > 5, y))],
    ]

    # note: the order of traverse is indeterminant
    actual_path_first = []
    actual_path_second = []
    for edge in cfg.get_edges():
        actual1 = edge.z3_constraints.get(1)
        actual2 = edge.z3_constraints.get(2)
        if actual1 is not None:
            actual_path_first.append(actual1)
        if actual2 is not None:
            actual_path_second.append(actual2)

    if len(actual_path_first) == len(expected_if_path):
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_first, expected_if_path)
        )
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_second, expected_other_path)
        )
    elif len(actual_path_first) == len(expected_other_path):
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_first, expected_other_path)
        )
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_second, expected_if_path)
        )
    else:
        assert False


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
    expected_if_path = [
        [z3.SubString(x, 0, 1) == "a", y > 5],
        [z3.SubString(x, 0, 1) == "a", y > 5, x == "abc"],
        [z3.SubString(x, 0, 1) == "a", y > 5, x == "abc"],
        [z3.SubString(x, 0, 1) == "a", y > 5, x == "abc"],
    ]
    expected_elif_path = [
        [z3.SubString(x, 0, 1) == "a", y > 5],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc")],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc"), y > 10],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc"), y > 10],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc"), y > 10],
    ]
    expected_else_path = [
        [z3.SubString(x, 0, 1) == "a", y > 5],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc")],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc"), z3.Not(y > 10)],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc"), z3.Not(y > 10)],
        [z3.SubString(x, 0, 1) == "a", y > 5, z3.Not(x == "abc"), z3.Not(y > 10)],
    ]

    actual_path_first = []
    actual_path_second = []
    actual_path_third = []
    for edge in cfg.get_edges():
        actual1 = edge.z3_constraints.get(1)
        actual2 = edge.z3_constraints.get(2)
        actual3 = edge.z3_constraints.get(3)
        if actual1 is not None:
            actual_path_first.append(actual1)
        if actual2 is not None:
            actual_path_second.append(actual2)
        if actual3 is not None:
            actual_path_third.append(actual3)

    for path in [actual_path_first, actual_path_second, actual_path_third]:
        assert any(
            (
                (set(actual) == set(expected) for actual, expected in zip(path, expected_if_path)),
                (
                    set(actual) == set(expected)
                    for actual, expected in zip(path, expected_elif_path)
                ),
                (
                    set(actual) == set(expected)
                    for actual, expected in zip(path, expected_else_path)
                ),
            )
        )


def test_while_loop() -> None:
    src = """
    def func(x: int, y: int) -> None:
        '''
        Preconditions:
            - x > 5
            - y > 10
        '''
        while x + y > 15:
            x -= 1
            y -= 1
        print(x + y)
    """
    cfg = _create_cfg(src, "func")
    x = z3.Int("x")
    y = z3.Int("y")
    expected_while_true_path = [[x > 5, y > 10], [x > 5, y > 10, x + y > 15]]
    expected_while_false_path = [
        [x > 5, y > 10],
        [x > 5, y > 10, z3.Not(x + y > 15)],
        [x > 5, y > 10, z3.Not(x + y > 15)],
    ]

    # note: the order of traverse is indeterminant
    actual_path_first = []
    actual_path_second = []
    for edge in cfg.get_edges():
        actual1 = edge.z3_constraints.get(1)
        actual2 = edge.z3_constraints.get(2)
        if actual1 is not None:
            actual_path_first.append(actual1)
        if actual2 is not None:
            actual_path_second.append(actual2)

    if len(actual_path_first) == len(expected_while_true_path):
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_first, expected_while_true_path)
        )
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_second, expected_while_false_path)
        )
    elif len(actual_path_first) == len(expected_while_false_path):
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_first, expected_while_false_path)
        )
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_second, expected_while_true_path)
        )
    else:
        assert False


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
    assert cfg.start.successors[0].z3_constraints == {1: [z3.Or(x == 1.0, x == 2.0, x == 3.0)]}
    assert cfg.end.predecessors[0].z3_constraints == {1: []}


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
    cfg = _create_cfg(src, "func")
    x = z3.Real("x")
    expected_if_path = [
        [z3.Or(x == 1.0, x == 2.0, x == 3.0)],
        [z3.Or(x == 1.0, x == 2.0, x == 3.0), x < 5],
        [],
        [],
    ]
    expected_else_path = [
        [z3.Or(x == 1.0, x == 2.0, x == 3.0)],
        [z3.Or(x == 1.0, x == 2.0, x == 3.0), z3.Not(x < 5)],
        [z3.Or(x == 1.0, x == 2.0, x == 3.0), z3.Not(x < 5)],
    ]

    actual_path_first = []
    actual_path_second = []
    for edge in cfg.get_edges():
        actual1 = edge.z3_constraints.get(1)
        actual2 = edge.z3_constraints.get(2)
        if actual1 is not None:
            actual_path_first.append(actual1)
        if actual2 is not None:
            actual_path_second.append(actual2)

    if len(actual_path_first) == len(expected_if_path):
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_first, expected_if_path)
        )
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_second, expected_else_path)
        )
    elif len(actual_path_first) == len(expected_else_path):
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_first, expected_else_path)
        )
        assert (
            set(actual) == set(expected)
            for actual, expected in zip(actual_path_second, expected_if_path)
        )
    else:
        assert False


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
    assert all(edge.z3_constraints == {1: [x > 5]} for edge in cfg.get_edges())


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
    edge_values = [value for edge in cfg.get_edges() for value in edge.z3_constraints.values()]
    assert all(value == [x > 5] for value in edge_values)


def test_ignored_while_condition() -> None:
    src = """
    def func(x: int) -> None:
        '''
        Preconditions:
            - x > 5
        '''
        a = 10
        while a > 5:
            print(a)
        print(x)
    """
    cfg = _create_cfg(src, "func")
    x = z3.Int("x")
    edge_values = [value for edge in cfg.get_edges() for value in edge.z3_constraints.values()]
    assert all(value == [x > 5] for value in edge_values)


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
