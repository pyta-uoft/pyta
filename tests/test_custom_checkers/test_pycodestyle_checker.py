import os

import astroid
import pylint.testutils
from astroid.brain.helpers import register_all_brains
from astroid.manager import AstroidManager

from python_ta.checkers.pycodestyle_checker import PycodestyleChecker

DIR_PATH = (
    os.path.abspath(os.path.join(__file__, "../../.."))
    + "/examples/custom_checkers/e9989_pycodestyle/"
)

MANAGER = AstroidManager()
register_all_brains(MANAGER)


class TestPycodestyleChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PycodestyleChecker

    def test_error_e222(self) -> None:
        mod = MANAGER.ast_from_file(DIR_PATH + "e222_error.py")
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
        mod = MANAGER.ast_from_file(DIR_PATH + "e222_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e262(self) -> None:
        mod = MANAGER.ast_from_file(DIR_PATH + "e262_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=1,
                node=None,
                args=("E262", "line 1, column 7: inline comment should start with '# '"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e262(self) -> None:
        mod = MANAGER.ast_from_file(DIR_PATH + "e262_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)


if __name__ == "__main__":
    import pytest

    print(CURRENT_DIR_PATH)
    pytest.main(["test_pycodestyle_checker.py"])
