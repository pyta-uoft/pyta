import os

import pylint.testutils
from astroid.astroid_manager import MANAGER

from python_ta.checkers.pycodestyle_checker import PycodestyleChecker

DIR_PATH = os.path.join(__file__, "../../../examples/custom_checkers/e9989_pycodestyle/")


class TestPycodestyleChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PycodestyleChecker
    CONFIG = {"pycodestyle_ignore": ["E24"]}

    def test_error_e123(self) -> None:
        """Tests that PEP8 error E123 closing bracket does not match indentation of opening bracket's line triggers"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e123_error.py"))
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=3,
                args=(
                    "E123",
                    "line 3, column 4: closing bracket does not match indentation of opening bracket's line",
                ),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e123(self) -> None:
        """Tests that PEP8 error E123 closing bracket does not match indentation of opening bracket's line
        is NOT triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e123_no_error.py"))
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e203(self) -> None:
        """Test that PEP8 error E203 (whitespace before ‘,’, ‘;’, or ‘:’) is triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e203_error.py"))
        args = ("E203", "line 1, column 30: whitespace before ':'")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-errors", line=1, args=args)
        ):
            self.checker.process_module(mod)

    def test_no_error_e203(self) -> None:
        """Test that PEP8 error E203 (whitespace before ‘,’, ‘;’, or ‘:’) is NOT triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e203_no_error.py"))
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e226(self) -> None:
        """Test that PEP8 error E226 (missing whitespace around arithmetic operator) is triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e226_error.py"))
        args = ("E226", "line 1, column 5: missing whitespace around arithmetic operator")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-errors", line=1, args=args)
        ):
            self.checker.process_module(mod)

    def test_no_error_e226(self) -> None:
        """Test that PEP8 error E226 (missing whitespace around arithmeic operator) is NOT triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e226_no_error.py"))
        with self.assertNoMessages():
            self.checker.process_module(mod)
