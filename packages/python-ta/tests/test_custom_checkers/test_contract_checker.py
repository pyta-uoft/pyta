import pylint.testutils
from astroid import nodes, parse

from python_ta.checkers.contract_checker import ContractChecker


class TestContractChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ContractChecker

    def test_invalid_operator(self) -> None:
        """Test that !== operator is caught as invalid syntax."""
        src = """
        def f(x: int) -> float:
            '''Return 1/x.

            Preconditions:
                - x !== 0
            '''
            return 1 / x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("x !== 0",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_assignment_statement(self) -> None:
        """Test that assignment statements are caught as invalid precondition syntax."""
        src = """
        def f(x: int, word: str) -> int:
            '''Return the word duplicated x times.

            Preconditions:
                - x = 5
                - word = "hello"
            '''
            return x*word
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("x = 5",),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=('word = "hello"',),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_incorrect_whitespace(self) -> None:
        """Test that incorrect whitespaces get flagged as bad syntax."""
        src = """
        def f(x: int) -> int:
            '''Return x**2

            Preconditions:
                - 0 < = x < 10
            '''
            return x**2
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("0 < = x < 10",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_missing_parenthesis(self):
        """Test that missing parenthesis are caught."""
        src = """
        def f(items: list) -> int:
            '''Return array length

            Preconditions:
                - len(items > 0
            '''
            return len(items)
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("len(items > 0",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_valid_preconditions(self) -> None:
        """Test that single-line preconditions with correct syntax pass."""
        src = """
        def f(x: int) -> int:
            '''Return 1/x

            Preconditions:
                - 1 <= x < 10
                - x == 5
                - x != 15
            '''
            return 1/x
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_valid_multi_line_preconditions(self) -> None:
        src = """
        def f(data: list, threshold: int) -> int:
            '''Return list length of a positive integer array

            Preconditions:
                - len(data) > 0 and \
                  all(isinstance(x, int) for x in data) and \
                  threshold >= 0
                - data != []
            '''
            return len(data)
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_invalid_multi_line_preconditions(self) -> None:
        src = """
        def f(data: list, threshold: int) -> int:
            '''Return list length of a positive integer array

            Preconditions:
                - len(data) > 0 and \
all(isinstance(x, int) for x in data) and \
threshold > = 0
                - data !== []
            '''
            return len(data)
        """

        mod = parse(src)
        func_node, *_ = mod.nodes_of_class(nodes.FunctionDef)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=(
                    "len(data) > 0 and all(isinstance(x, int) for x in data) and threshold > = 0",
                ),
            ),
            pylint.testutils.MessageTest(
                msg_id="invalid-precondition-syntax",
                node=func_node,
                args=("data !== []",),
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)
