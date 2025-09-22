from unittest.mock import patch

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
                msg_id="infinite-loop", node=node.test, confidence=INFERENCE
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_attr_not_updated(self) -> None:
        """Test that the checker correctly flags a while loop when no condition variable attributes are used in
        the loop body."""
        src = """
        class Faa:
            def __init__(self):
                self.attribute = 10
            def foo(self):
                while 0 < self.attribute < 100: #@
                    attribute += 1
        """

        node = astroid.extract_node(src)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="infinite-loop", node=node.test, confidence=INFERENCE
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    def test_attr_not_updated_cond_false(self) -> None:
        """Test that the checker correctly flags a while loop when no condition variable attributes are used in
        the loop body."""
        src = """
        class Faa:
            def __init__(self):
                self.attribute = 0
            def foo(self):
                while 0 < self.attribute < 100: #@
                    attribute += 1
        """

        node = astroid.extract_node(src)

        with self.assertNoMessages():
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
                msg_id="infinite-loop", node=detected_node.test, confidence=INFERENCE
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
                msg_id="infinite-loop", node=node.test, confidence=INFERENCE
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
                msg_id="infinite-loop", node=node.test, confidence=INFERENCE
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

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
                confidence=INFERENCE,
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
        while 2: #@
            break
        while 3: #@
            yield
        while 4: #@
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
        while not []: #@
            x += 1
        """,
            """
        while not {}: #@
            x += 1
        """,
            """
        while not (): #@
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
            """
        while {1, 2}: #@
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
                confidence=INFERENCE,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(node)

    @pytest.mark.parametrize(
        "src",
        [
            """
        def foo():
            return

        while foo: #@
            x += 1
        """,
            """
        faa = lambda: True

        while faa: #@
            x += 1
        """,
            """
        while (lambda: True): #@
            x += 1
        """,
        ],
    )
    def test_while_func_obj_condition(self, src: str) -> None:
        """Test verifies that infinite-loop warning is triggered when a function object is used inside loop
        condition."""
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

    def test_constant_infer_fail(self) -> None:
        """Test verifies that `_check_condition_constant` helper handles failed inference correctly."""
        """"""
        src = """
        while x: #@
            pass
        """
        node = astroid.extract_node(src)

        def fake_infer(node, *args, **kwargs):
            if isinstance(node, astroid.nodes.Name):
                yield astroid.util.Uninferable()
            else:
                yield from astroid.nodes.NodeNG.infer(node, *args, **kwargs)

        with patch.object(astroid.nodes.NodeNG, "infer", fake_infer):
            result = self.checker._check_condition_constant(node)
            assert result is False

    @pytest.mark.parametrize(
        "src",
        [
            """
        while []: #@
            x += 1
        """,
            """
        while {}: #@
            x += 1
        """,
            """
        while (): #@
            x += 1
        """,
            """
        while not {1, 2}: #@
            x += 1
        """,
            """
        while 0: #@
            x += 1
        """,
            """
        while not 101: #@
            x += 1
        """,
            """
        while 2 < 1: #@
            x += 1
        """,
        ],
    )
    def test_constant_fail(self, src: str) -> None:
        """Test verifies that `_check_condition_constant` helper handles case where inferred value is False."""
        node = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker._check_condition_constant(node)

    @pytest.mark.parametrize(
        "src",
        [
            """
            i = 0
            while i < 1: #@
                print(i)
            """,
            """
            i = 0.1
            while i < 1: #@
                print(i)
            """,
            """
            i = 1 + 3j
            while i: #@
                print(i)
            """,
            """
            i = True
            while i: #@
                print(i)
            """,
            """
            i =  "hello"
            while i != "hi": #@
                print(i)
            """,
            """
            i =  b"hello"
            while i != "hi": #@
                print(i)
            """,
            """
            i = (1, 2)
            while i: #@
                print(i)
            """,
            """
            i = None
            while not i: #@
                print(i)
            """,
            """
            i, j, k, l = 1, 0.9, True, "Goodbye"
            while i + j < 10 and not k or l != "cool": #@
                print(i, j, k, l)
            """,
        ],
    )
    def test_immutable_cond_vars(self, src: str) -> None:
        """Test verifies that `_check_immutable_cond_var_reassigned` flags infinite loops with immutable condition
        variables and no re-assignment in the body."""
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

    @pytest.mark.parametrize(
        "src",
        [
            """
            i = 0
            while i > 1: #@
                print(i)
            """,
            """
            i = True
            while not i: #@
                print(i)
            """,
            """
            i = ""
            while i != "ooooooo": #@
                i = i + "o"
            """,
            """
            i, j, k, l = 1, 0.9, True, "Goodbye"
            while i + j > 10 or not k or l == "cool": #@
                print(i, j, k, l)
            """,
            """
            i, j, k, l = 1, 0.9, True, "Goodbye"
            while i + j < 10 and not k or l != "cool": #@
                print(i, j, k, l)
                i += 1
            """,
            """
            lst = [1, 2]
            i = 0
            while lst != [10] and i < 10: #@
                print(lst)
                foo(i)
                lst[0] = i
            """,
        ],
    )
    def test_immutable_cond_vars_fail(self, src: str) -> None:
        """Test verifies that `_check_immutable_cond_var_reassigned` does not flag loops that do satisfy the conditions
        of the check."""
        node = astroid.extract_node(src)

        with self.assertNoMessages():
            self.checker.visit_while(node)

    def test_immutable_fail_infer_var(self) -> None:
        """Test verifies that `_check_immutable_cond_var_reassigned` handles failed infer properly for condition
        var."""
        src = """
        i = 0
        while i < 100: #@
            print(i)
        """
        node = astroid.extract_node(src)

        with patch("astroid.nodes.NodeNG.infer", return_value=[astroid.util.Uninferable()]):
            result = self.checker._check_immutable_cond_var_reassigned(node)
            assert result is False

    def test_immutable_fail_infer_cond(self) -> None:
        """Test verifies that `_check_immutable_cond_var_reassigned` handles failed infer properly for condition."""
        src = """
        i = 0
        while i < 100: #@
            print(i)
        """
        node = astroid.extract_node(src)

        def fake_infer(node):
            if isinstance(node, astroid.nodes.Compare):
                yield astroid.util.Uninferable()
            elif isinstance(node, astroid.nodes.Name):
                yield astroid.nodes.Const(value=0)

        with patch.object(astroid.nodes.NodeNG, "infer", fake_infer):
            result = self.checker._check_immutable_cond_var_reassigned(node)
            assert result is False


class TestConstantConditionHelper(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InfiniteLoopChecker

    NOT_CONSTANT_CASES = [
        """
    while faa(all(x)) and lst[1][2]["yellow"].get_address() or func(var, foo(all(z, 10))): #@
        y += 1
    """,
        """
    def foo():
        i = 10
        while i < 21: #@
            i += 1
            j = 19
    """,
        """
    while 0 < self.attribute < 100: #@
            attribute += 1
    """,
        """
    i, k, l = 0, 20, 40
    j = 10
    while i < 100 and k < 21 or l < 40: #@
        j += 1
        j = j - 1
    """,
        """
    while foo(10): #@
        x += 1
    """,
        """
    while foo(10) < 21 and faa(x): #@
        x += 1
    """,
    ]

    CONSTANT_CASES = [
        """
    while 1: #@
        x += 1
    """,
        """
    while True: #@
        x += 1
    """,
        """
    while []: #@
        x += 1
    """,
        """
    while {}: #@
        x += 1
    """,
        """
    while (): #@
        x += 1
    """,
    ]

    CONSTANT_COMP_CASES = [
        """
    while 1 < 2: #@
        x += 1
    """,
        """
    while True and 1 < 2 or 0: #@
        x += 1
    """,
        """
    while not (): #@
        x += 1
    """,
        """
    while not []: #@
        x += 1
    """,
        """
    while not {}: #@
        x += 1
    """,
    ]

    @pytest.mark.parametrize("src", CONSTANT_COMP_CASES)
    def test_constant_comp_condition_correctness(self, src: str) -> None:
        """Test verifies that `_check_constant_form_condition` helper properly flags constant BoolOp or BinOp loop
        conditions."""
        node = astroid.extract_node(src)

        expected = True
        actual = self.checker._check_constant_form_condition(node)
        assert actual == expected

    @pytest.mark.parametrize("src", NOT_CONSTANT_CASES)
    def test_not_constant_comp_condition_correctness(self, src: str) -> None:
        """Test verifies that `_check_constant_form_condition` helper does not flag non-constant loop conditions."""
        node = astroid.extract_node(src)

        expected = False
        actual = self.checker._check_constant_form_condition(node)
        assert actual == expected

    @pytest.mark.parametrize("src", CONSTANT_CASES)
    def test_constant_condition_correctness(self, src: str) -> None:
        """Test verifies that `_check_constant_loop_cond` helper properly flags constant loop conditions."""
        node = astroid.extract_node(src)

        expected = True
        actual = self.checker._check_constant_loop_cond(node.test)
        assert actual == expected

    @pytest.mark.parametrize("src", NOT_CONSTANT_CASES)
    def test_not_constant_condition_correctness(self, src: str) -> None:
        """Test verifies that `_check_constant_loop_cond` helper does not flag non-constant loop conditions."""
        node = astroid.extract_node(src)

        expected = False
        actual = self.checker._check_constant_loop_cond(node.test)
        assert actual == expected

    def test_constant_condition_infer_fail(self) -> None:
        """Test verifies that `_check_constant_loop_cond` helper handles failed inference correctly."""
        """"""
        src = """
        while x: #@
            pass
        """
        node = astroid.extract_node(src)

        with patch("pylint.checkers.utils.safe_infer", return_value=astroid.util.UninferableBase()):
            result = self.checker._check_constant_loop_cond(node.test)
            assert result is False
