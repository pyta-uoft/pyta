"""Test suite for testing the InvalidRangeIndexChecker."""
import astroid
import pylint.testutils

from python_ta.checkers.invalid_range_index_checker import InvalidRangeIndexChecker


class TestInvalidNameChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InvalidRangeIndexChecker

    def _test_invalid(self, src):
        mod = astroid.parse(src)
        node, *_ = mod.nodes_of_class(astroid.nodes.Call)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="invalid-range-index", node=node, line=1, args="1"),
            ignore_position=True,
        ):
            self.checker.visit_call(node)

    def _test_valid(self, src):
        mod = astroid.parse(src)
        node, *_ = mod.nodes_of_class(astroid.nodes.Call)

        with self.assertNoMessages():
            self.checker.visit_call(node)

    def test_zero_param(self) -> None:
        """Tests range()"""

        self._test_invalid("range()")

    def test_one_param(self) -> None:
        """Tests range(x) where x >= 2"""

        self._test_valid("range(5)")

    def test_invalid_one_param(self) -> None:
        """Tests range(x) where x < 2"""

        self._test_invalid("range(1)")
        self._test_invalid("range(0)")
        self._test_invalid("range(-1)")

    def test_two_param(self) -> None:
        """Tests range(x, y) where y - x >= 2"""

        self._test_valid("range(2, 5)")

    def test_invalid_two_param(self) -> None:
        """Tests range(x, y) where y - x < 2"""

        self._test_invalid("range(2, 3)")
        self._test_invalid("range(2, 2)")
        self._test_invalid("range(2, 1)")

    def test_non_int_param(self) -> None:
        """Tests range(x) where x is not int"""

        self._test_invalid("range(5.5)")

    def test_three_param(self) -> None:
        """Tests range(x, y, z) where y - x < 2"""

        self._test_valid("range(1, 5, 3)")
        self._test_valid("range(5, 1, -3)")

    def test_three_param_big_inc(self) -> None:
        """Tests range(x, y, z) where abs(z) > abs(x - y)"""

        self._test_invalid("range(1, 5, 12)")
        self._test_invalid("range(1, 5, -12)")
        self._test_invalid("range(1, -5, 12)")
        self._test_invalid("range(-1, -5, 12)")

    def test_three_param_zero_inc(self) -> None:
        """Tests range(x, y, z) where z = 0"""

        self._test_invalid("range(1, 5, 0)")

    def test_three_param_opposite_inc(self) -> None:
        """Tests range(x, y, z) where z is going in the wrong direction"""

        self._test_invalid("range(1, 5, -2)")
        self._test_invalid("range(5, 1, 2)")
