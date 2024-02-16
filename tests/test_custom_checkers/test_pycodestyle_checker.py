import os

import astroid
import pylint.testutils
from astroid.brain.helpers import register_all_brains
from astroid.manager import AstroidManager

from python_ta.checkers.pycodestyle_checker import PycodestyleChecker

CURRENT_DIR_PATH = os.path.dirname(os.path.realpath(__file__))

MANAGER = AstroidManager()
register_all_brains(MANAGER)


class TestPycodestyleChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PycodestyleChecker

    def test_error_e222(self) -> None:
        mod = MANAGER.ast_from_file(
            CURRENT_DIR_PATH + "test_e9989_pycodestyle/error_e222_example.py"
        )
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=1,
                node=None,
                args=("E222", "line 1, column 3: multiple spaces after operator"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e222(self) -> None:
        mod = MANAGER.ast_from_file(
            CURRENT_DIR_PATH + "test_e9989_pycodestyle/no_error_e222_example.py"
        )
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e262(self) -> None:
        mod = MANAGER.ast_from_file(
            CURRENT_DIR_PATH + "test_e9989_pycodestyle/error_e262_example.py"
        )
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=1,
                node=None,
                args=("E262", "line 1, column 8: inline comment should start with '# '"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e262(self) -> None:
        mod = MANAGER.ast_from_file(
            CURRENT_DIR_PATH + "test_e9989_pycodestyle/no_error_e262_example.py"
        )
        with self.assertNoMessages():
            self.checker.process_module(mod)


if __name__ == "__main__":
    import pytest

    pytest.main(["test_pycodestyle_checker.py"])
