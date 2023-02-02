"""Test suite for testing the ForbiddenPythonSyntaxChecker."""
import astroid
import pylint.testutils
from astroid import nodes

from python_ta.checkers.forbidden_python_syntax_checker import (
    ForbiddenPythonSyntaxChecker,
)


class TestForbiddenPythonSyntaxCheckerDisallowedsyntax(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ForbiddenPythonSyntaxChecker
    CONFIG = {}

    def set_up(self) -> None:
        """Perform the set up before each test case executes."""
        self.setup_method()

    def test_disallow_break_in_code(self) -> None:
        """Test that the checker correctly reports a break statement in the code when its usage is
        disallowed.
        """
        src = """
        for i in range(0, 10):
            break
        """
        mod = astroid.parse(src)
        break_node, *_ = mod.nodes_of_class(nodes.Break)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="forbidden-break-usage", node=break_node),
            ignore_position=True,
        ):
            self.checker.visit_break(break_node)

    def test_disallow_continue_in_code(self) -> None:
        """Test that the checker correctly reports a continue statement in the code when its usage
        is disallowed.
        """
        src = """
        for i in range(0, 10):
            continue
        """
        mod = astroid.parse(src)
        continue_node, *_ = mod.nodes_of_class(nodes.Continue)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="forbidden-continue-usage", node=continue_node),
            ignore_position=True,
        ):
            self.checker.visit_continue(continue_node)

    def test_disallow_comprehension_in_code(self) -> None:
        """Test that the checker correctly reports a comprehension in the code when its usage is
        disallowed.
        """
        src = """
        comp = [i ** 2 for i in range(1, 11)]
        """
        mod = astroid.parse(src)
        comprehension_node, *_ = mod.nodes_of_class(nodes.Comprehension)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-comprehension-usage", node=comprehension_node
            ),
            ignore_position=True,
        ):
            self.checker.visit_comprehension(comprehension_node)

    def test_disallow_for_loop_in_code(self) -> None:
        """Test that the checker correctly reports a for loop in the code when its usage is
        disallowed.
        """
        src = """
        for i in range(0, 10):
            print(i)
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(nodes.For)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="forbidden-for-loop-usage", node=for_node),
            ignore_position=True,
        ):
            self.checker.visit_for(for_node)

    def test_disallow_while_loop_in_code(self) -> None:
        """Test that the checker correctly reports a while loop in the code when its usage is
        disallowed.
        """
        src = """
        count = 10
        while count > -1:
            count -= 1
        """
        mod = astroid.parse(src)
        while_node, *_ = mod.nodes_of_class(nodes.While)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="forbidden-while-loop-usage", node=while_node),
            ignore_position=True,
        ):
            self.checker.visit_while(while_node)


class TestForbiddenPythonSyntaxCheckerAllowedsyntax(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ForbiddenPythonSyntaxChecker
    CONFIG = {"allowed_python_syntax": ["break", "continue", "comprehension", "for", "while"]}

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
            self.checker.visit_break(break_node)

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
            self.checker.visit_continue(continue_node)

    def test_allow_comprehension_in_code(self) -> None:
        """Test that the checker correctly doesn't report a comprehension when its usage is allowed."""
        src = """
        comp = [i ** 2 for i in range(1, 11)]
        """
        mod = astroid.parse(src)
        comprehension_node, *_ = mod.nodes_of_class(nodes.Comprehension)

        with self.assertNoMessages():
            self.checker.visit_comprehension(comprehension_node)

    def test_allow_for_in_code(self) -> None:
        """Test that the checker correctly doesn't report a for loop when its usage is allowed."""
        src = """
        for i in range(0, 10):
            print(i)
        """
        mod = astroid.parse(src)
        for_node, *_ = mod.nodes_of_class(nodes.For)

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

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
            self.checker.visit_while(while_node)


if __name__ == "__main__":
    import pytest

    pytest.main(["test_forbidden_python_syntax_checker.py"])
