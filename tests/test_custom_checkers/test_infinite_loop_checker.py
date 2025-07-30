import astroid
import pylint.testutils
import pytest
from pylint.interfaces import INFERENCE

from python_ta.checkers.infinite_loop_checker import InfiniteLoopChecker


class TestInfiniteLoopChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InfiniteLoopChecker

    def test_var_not_updated(self) -> None:
        """Test that the checker correctly flags a while loop when no condition variables are used in the loop body."""
        src = """
            i, k, l = 0, 20, 40
            j = 10
            while i < 100 and k < 21 or l < 40: #@
                j += 1
                j = j - 1
        """

        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=node.test,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_attr_not_updated(self) -> None:
        """Test that the checker correctly flags a while loop when no condition variable attributes are used in
        the loop body."""
        src = """
        while 0 < self.attribute < 100: #@
            attribute += 1
        """

        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=node.test,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_nested_while_unused_var(self) -> None:
        """Test that the checker flags a nested while loop where none of its condition variables are used in its body"""
        src = """
        i = 0
        j = 10
        k = "David is cool!"
        while i < 10: #@
            while i < j: #@
                k += '!'
            i += 1
        """

        node, detected_node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=detected_node.test,
            ),
            ignore_position=True,
        ):
            for node in node.nodes_of_class(astroid.While):
                self.checker.visit_while(node)

    def test_while_inside_func_unused_var(self) -> None:
        """Test that the checker flags infinite while loops inside function."""
        src = """
        def foo():
            i = 10
            while i < 21: #@
                j = 19
        """
        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=node.test,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_subscript_notation(self) -> None:
        """Test that the checker flags a while loop that uses a subscript annotated variable."""
        src = """
        lst = [1, 2, 3]
        i = 0
        while lst[1] > 1: #@
            i += 1
        """

        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=node.test,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_condition_variable_used_only_as_argument(self):
        """Test that the checker does not flag while loops when the condition variable is passed to a function
        or method."""
        src = """
        i = 0
        while i < 20: #@
            self.update(i)

        while i < 20: #@
            increment(i)
        """

        node1, node2 = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node1)
            self.checker.visit_while(node2)

    def test_multiple_while_pass(self) -> None:
        """Test that the checker does not flag non-infinite while loops."""
        src = """
        i = 0
        j = 10
        while i < 10: #@
            i += 2
        while j < 20: #@
            j += 1
        """

        node1, node2 = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node1)
            self.checker.visit_while(node2)

    def test_while_inside_func_pass(self) -> None:
        """Test that the checker does not flag non-infinite while loops inside function."""
        src = """
        def foo():
            i = 10
            while i < 21: #@
                i += 1
                j = 19
        """
        node = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node)

    def test_while_true_enabled(self) -> None:
        """Test that loops with no condition variables is not flagged."""
        src = """
        x = 0
        while True: #@
            x += 1
        """

        node = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node)

    def test_while_func_call(self) -> None:
        """Test verifies that function calls in while-loop conditions do not incorrectly trigger infinite-loop
        warnings."""
        src = """
        while foo(10): #@
            x += 1
        while foo(10) < 21 and faa(x): #@
            x += 1
        """
        node1, node2 = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node1)
            self.checker.visit_while(node2)

    def test_while_fund_call_var(self) -> None:
        """Test verifies that function calls in while-loop conditions correctly triggers infinite-loop
        warnings."""
        src = """
        while faa(all(x)) and lst[1][2]["yellow"].get_address() or func(var, foo(all(z, 10))): #@
            y += 1 # Should trigger an infinite loop since condition variables set: {'lst', 'var', 'z', 'x'}
        """
        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=node.test,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_while_inferred_exit(self) -> None:
        """Test verifies that infinite-loop warning is not triggered when loop condition is constant but 'sys.exit' is
        called using alias."""
        src = """
        import sys as x

        second_alias = x

        while 1 < 2 and True: #@
            second_alias.exit()
        """
        node = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node)

    def test_while_normal_exit(self) -> None:
        """Test verifies that infinite-loop warning is not triggered when loop condition is constant but 'sys.exit' is
        called."""
        src = """
        import sys

        while 1 < 2 and True: #@
            sys.exit()
        """
        node = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node)

    def test_while_false_exit(self) -> None:
        """Test verifies that infinite-loop warning is triggered when loop condition is constant and a "false" exit
        is used."""
        src = """
        while 1 < 2: #@
            attr.exit() # Should raise a warning since `sys` was never aliased to `attr` and condition constant
        """

        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=node.test,
                confidence=INFERENCE,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_while_different_loop_exiting_statements(self) -> None:
        """Test verifies that infinite-loop warning is not triggered when loop condition is constant but different
        loop exiting statements are called."""
        src = """
        while 1: #@
            return
        while 1: #@
            break
        while 1: #@
            yield
        while 1: #@
            raise
        """
        nodes = list(astroid.extract_node(src))

        with self.assertNoMessages():
            for node in nodes:
                self.checker.visit_while(node)

    @pytest.mark.parametrize(
        "src",
        [
            """
        while 1: #@
            x += 1
        """,
            """
        while True: #@
            x += 1
        """,
            """
        while 1 < 2: #@
            x += 1
        """,
            """
        while True and 1 < 2 or 0: #@
            x += 1
        """,
        ],
    )
    def test_while_constant_loop_condition(self, src: str) -> None:
        """Test verifies that infinite-loop warning is triggered when loop condition is constant and no loop exiting
        statement is called"""
        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop",
                node=node.test,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)
