"""Test suite for testing the ForbiddenPythonSyntaxChecker."""

import astroid
import pylint.testutils
import pytest
from astroid import nodes

from python_ta.checkers.forbidden_python_syntax_checker import (
    ForbiddenPythonSyntaxChecker,
)


class TestForbiddenPythonSyntaxCheckerDisallowedsyntax(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ForbiddenPythonSyntaxChecker
    CONFIG = {"disallowed_python_syntax": ["Break", "Continue", "Comprehension", "For", "While"]}

    def set_up(self) -> None:
        """Perform the set up before each test case executes."""
        self.setup_method()

    @pytest.mark.parametrize(
        "src, expected_node_type",
        [
            (
                """
            for i in range(0, 10):
                break
            """,
                nodes.Break,
            ),
            (
                """
            for i in range(0, 10):
                continue
            """,
                nodes.Continue,
            ),
            (
                """
            comp = [i ** 2 for i in range(1, 11)]
            """,
                nodes.Comprehension,
            ),
            (
                """
            for i in range(0, 10):
                print(i)
            """,
                nodes.For,
            ),
            (
                """
            count = 10
            while count > -1:
                count -= 1
            """,
                nodes.While,
            ),
        ],
        ids=[
            "test_disallow_break_in_code",
            "test_disallow_continue_in_code",
            "test_disallow_comprehension_in_code",
            "test_disallow_for_loop_in_code",
            "test_disallow_while_loop_in_code",
        ],
    )
    def test_disallowed_syntax(self, src: str, expected_node_type: type) -> None:
        """Test that the checker correctly reports disallowed Python syntax constructs."""
        mod = astroid.parse(src)
        node, *_ = mod.nodes_of_class(expected_node_type)
        name = node.__class__.__name__

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="forbidden-python-syntax", node=node, args=name),
            ignore_position=True,
        ):
            self.checker.visit_default(node)


class TestForbiddenPythonSyntaxCheckerAllowedsyntax(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ForbiddenPythonSyntaxChecker
    CONFIG = {}

    def set_up(self) -> None:
        """Perform the set up before each test case executes."""
        self.setup_method()

    def test_allow_break_in_code(self) -> None:
        """Test that the checker correctly doesn't report a break statement when its usage is
        allowed.
        """
        src = """
        for i in range(0, 10):
            break
        """
        mod = astroid.parse(src)
        break_node, *_ = mod.nodes_of_class(nodes.Break)

        with self.assertNoMessages():
            self.checker.visit_default(break_node)

    def test_allow_continue_in_code(self) -> None:
        """Test that the checker correctly doesn't report a continue statement when its usage is
        allowed.
        """
        src = """
        for i in range(0, 10):
            continue
        """
        mod = astroid.parse(src)
        continue_node, *_ = mod.nodes_of_class(nodes.Continue)

        with self.assertNoMessages():
            self.checker.visit_default(continue_node)

    def test_allow_comprehension_in_code(self) -> None:
        """Test that the checker correctly doesn't report a comprehension when its usage is allowed."""
        src = """
        comp = [i ** 2 for i in range(1, 11)]
        """
        mod = astroid.parse(src)
        comprehension_node, *_ = mod.nodes_of_class(nodes.Comprehension)

        with self.assertNoMessages():
            self.checker.visit_default(comprehension_node)

    def test_allow_for_in_code(self) -> None:
        """Test that the checker correctly doesn't report a for loop when its usage is allowed."""
        src = """
        for i in range(0, 10):
            print(i)
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(nodes.For)

        with self.assertNoMessages():
            self.checker.visit_default(for_node)

    def test_allow_while_in_code(self) -> None:
        """Test that the checker correctly doesn't report a while loop when its usage is allowed."""
        src = """
        count = 10
        while count > -1:
            count -= 1
        """
        mod = astroid.parse(src)
        while_node, *_ = mod.nodes_of_class(nodes.While)

        with self.assertNoMessages():
            self.checker.visit_default(while_node)


if __name__ == "__main__":
    import pytest

    pytest.main(["test_forbidden_python_syntax_checker.py"])
