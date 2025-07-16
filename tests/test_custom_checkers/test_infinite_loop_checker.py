import astroid
import pylint.testutils
import pytest

from python_ta.checkers.infinite_loop_checker import InfiniteLoopChecker


class TestInfiniteLoopChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InfiniteLoopChecker
    WHILE_TRUE = [
        """
        var = 0
        while True:
            var += 1
        """,
        """
        var = 0
        while 1:
            var += 1
        """,
        """
        var = 0
        while 1 < 2:
            var += 1
        """,
    ]

    def test_var_not_updated(self) -> None:
        """Test that the checker correctly flags a while loop when no condition variables are used in the loop body."""
        src = """
            i = 0
            j = 10
            while i < 100:
                j += 1
                j = j - 1
        """
        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.While)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="loop-condition-variable-unused",
                node=node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)
            self.checker.leave_while(node)

    def test_attr_not_updated(self) -> None:
        """Test that the checker correctly flags a while loop when no condition variable attributes are used in
        the loop body."""
        src = """
        while 0 < self.attribute < 100:
            attribute += 1
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.While)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="loop-condition-variable-unused",
                node=node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)
            self.checker.leave_while(node)

    def test_nested_while_unused_var(self) -> None:
        """Test that the checker flags a nested while loop where none of its condition variables are used in its body"""
        src = """
        i = 0
        j = 10
        k = "David is cool!"
        while i < 10:
            while i < j:
                k += '!'
            i += 1
        """

        mod = astroid.parse(src)

        nodes = list(mod.nodes_of_class(astroid.nodes.While))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="loop-condition-variable-unused",
                node=nodes[1],
            ),
            ignore_position=True,
        ):
            for node in mod.nodes_of_class(astroid.nodes.While):
                self.checker.visit_while(node)
                self.checker.leave_while(node)

    def test_while_inside_func_unused_var(self) -> None:
        """Test that the checker flags infinite while loops inside function."""
        src = """
        def foo():
            i = 10
            while i < 21:
                j = 19
        """
        mod = astroid.parse(src)

        node = list(mod.nodes_of_class(astroid.nodes.While))

        with self.assertNoMessages(
            pylint.testutils.MessageTest(
                msg_id="loop-condition-variable-unused",
                node=node[0],
            ),
            ignore_position=True,
        ):
            for node in mod.nodes_of_class(astroid.nodes.While):
                self.checker.visit_while(node)
                self.checker.leave_while(node)

    def test_multiple_while_pass(self) -> None:
        """Test that the checker does not flag non-infinite while loops."""
        src = """
        i = 0
        j = 10
        while i < 10:
            i += 2
        while j < 20:
            j += 1
        """

        mod = astroid.parse(src)

        with self.assertNoMessages():
            for node in mod.nodes_of_class(astroid.nodes.While):
                self.checker.visit_while(node)
                self.checker.leave_while(node)

    def test_while_inside_func_pass(self) -> None:
        """Test that the checker does not flag non-infinite while loops inside function."""
        src = """
        def foo():
            i = 10
            while i < 21:
                i += 1
                j = 19
        """
        mod = astroid.parse(src)

        with self.assertNoMessages():
            for node in mod.nodes_of_class(astroid.nodes.While):
                self.checker.visit_while(node)
                self.checker.leave_while(node)

    @pytest.mark.parametrize("src", WHILE_TRUE)
    def test_while_true_enabled(self, src: str) -> None:
        """Test that loops of the form 'while True' are not flagged when the 'allow-while-true' option is enabled."""
        self.linter.set_option("allow-while-true", True)

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.While)

        with self.assertNoMessages():
            self.checker.visit_while(node)
            self.checker.leave_while(node)

    @pytest.mark.parametrize("src", WHILE_TRUE)
    def test_while_true_disabled(self, src: str) -> None:
        """Test that loops of the form 'while True' are flagged when the 'allow-while-true' option is disabled."""
        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.While)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="while-true-loop",
                node=node.test,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)
            self.checker.leave_while(node)
