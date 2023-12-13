import astroid
import astroid.nodes as nodes
import pylint.testutils

from python_ta.checkers.invalid_range_index_checker import InvalidRangeIndexChecker


class TestInvalidRangeIndexChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidRangeIndexChecker

    def test_valid_range_one_arg(self):
        src = """
        range(10)
        """
        range_node = astroid.extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_call(range_node)

    def test_valid_range_two_arg(self):
        src = """
        range(2, 8)
        """
        range_node = astroid.extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_call(range_node)

    def test_valid_range_three_arg(self):
        src = """
        range(2, 8, 2)
        """
        range_node = astroid.extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_call(range_node)

    def test_valid_range_three_arg_negative(self):
        src = """
        range(-10, -20, -2)
        """
        range_node = astroid.extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_call(range_node)

    def test_invalid_range_empty(self):
        src = """
        range()
        """
        range_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-range-index",
                node=range_node,
                args="2",
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(range_node)

    def test_invalid_range_one_arg(self):
        src = """
        range(-10)
        """
        range_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-range-index",
                node=range_node,
                args="2",
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(range_node)

    def test_invalid_range_two_arg(self):
        src = """
        range(5, 6)
        """
        range_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-range-index",
                node=range_node,
                args="2",
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(range_node)

    def test_invalid_range_three_arg(self):
        src = """
        range(2, 15, 20)
        """
        range_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-range-index",
                node=range_node,
                args="2",
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(range_node)

    def test_invalid_range_zero_step(self):
        src = """
        range(1, 10, 0)
        """
        range_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-range-index",
                node=range_node,
                args="2",
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(range_node)

    def test_wrong_type(self):
        src = """
        range("hello", "bye")
        """
        range_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="invalid-range-index",
                node=range_node,
                args="2",
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(range_node)

    def test_uninferable(self):
        src = """
        range(0, [][1])
        """
        range_node = astroid.extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_call(range_node)

    def test_variables_undefined(self):
        src = """
        range(start, stop)  # These variables are undefined
        """
        range_node = astroid.extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_call(range_node)

    def test_variables_defined(self):
        src = """
        start = 1
        stop = 10
        range(start, -stop)
        """
        range_node = astroid.extract_node(src)
        # Even though these variables can have their values inferred,
        # we are conservative and do not attempt inference (see test_variables_ambiguous below).
        with self.assertNoMessages():
            self.checker.visit_call(range_node)

    def test_variables_ambiguous(self):
        src = """
        def f(numbers):
            result = []
            for _ in numbers:
                result.append(1)

            range(len(result))  #@
        """
        range_node = astroid.extract_node(src)
        # In this case, result is currently being inferred as an empty list [],
        # but may not be empty. So to be conservative we do not attempt to infer
        # its result, and instead skip checking this range expression.
        with self.assertNoMessages():
            self.checker.visit_call(range_node)


if __name__ == "__main__":
    import pytest

    pytest.main(["test_invalid_range_index_checker.py"])
