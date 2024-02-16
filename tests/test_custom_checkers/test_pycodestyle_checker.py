"""Tests for PycodestyleChecker"""
import os

import astroid
import pycodestyle
import pylint.testutils
from astroid.astroid_manager import MANAGER

from python_ta.checkers.pycodestyle_checker import PycodestyleChecker


class TestPycodestyleChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PycodestyleChecker
    CONFIG = {"pycodestyle_ignore": ["E111"]}

    def test_error_e123(self) -> None:
        """Tests for `import XX` statements"""

        test_file = os.path.abspath(__file__ + "/../e123.py")

        mod = MANAGER.ast_from_file(test_file)

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


class JSONReport(pycodestyle.StandardReport):
    def get_file_results(self):
        self._deferred_print.sort()
        return [
            (line_number, f"line {line_number}, column {offset}: {text}", code)
            for line_number, offset, code, text, _ in self._deferred_print
        ]
