import os

import pylint.testutils
import pytest
from astroid.astroid_manager import MANAGER

from python_ta.checkers.pycodestyle_checker import PycodestyleChecker

DIR_PATH = os.path.join(__file__, "../../../examples/custom_checkers/e9989_pycodestyle/")

# Define parameter sets for different error and no-error tests
error_params = [
    ("e115_error.py", "E115", 2, 0, "expected an indented block (comment)"),
    ("e122_error.py", "E122", 2, 0, "continuation line missing indentation or outdented"),
    (
        "e123_error.py",
        "E123",
        3,
        4,
        "closing bracket does not match indentation of opening bracket's line",
    ),
    ("e125_error.py", "E125", 2, 4, "continuation line with same indent as next logical line"),
    ("e127_error.py", "E127", 2, 19, "continuation line over-indented for visual indent"),
    ("e129_error.py", "E129", 4, 4, "visually indented line with same indent as next logical line"),
    ("e131_error.py", "E131", 4, 8, "continuation line unaligned for hanging indent"),
    ("e203_error.py", "E203", 1, 30, "whitespace before ':'"),
    ("e222_error.py", "E222", 1, 3, "multiple spaces after operator"),
    ("e223_error.py", "E223", 1, 1, "tab before operator"),
    ("e224_error.py", "E224", 1, 3, "tab after operator"),
    ("e226_error.py", "E226", 1, 5, "missing whitespace around arithmetic operator"),
    ("e227_error.py", "E227", 1, 5, "missing whitespace around bitwise or shift operator"),
    ("e228_error.py", "E228", 1, 5, "missing whitespace around modulo operator"),
    ("e262_error.py", "E262", 1, 7, "inline comment should start with '# '"),
    ("e265_error.py", "E265", 1, 0, "block comment should start with '# '"),
    ("e266_error.py", "E266", 1, 0, "too many leading '#' for block comment"),
    ("e275_error.py", "E275", 1, 16, "missing whitespace after keyword"),
    ("e301_error.py", "E301", 5, 4, "expected 1 blank line, found 0"),
    ("e303_error.py", "E303", 6, 0, "too many blank lines (3)"),
    ("e304_error.py", "E304", 12, 0, "blank lines found after function decorator"),
]

no_error_params = [
    "e115_no_error.py",
    "e122_no_error.py",
    "e123_no_error.py",
    "e125_no_error.py",
    "e127_no_error.py",
    "e129_no_error.py",
    "e131_no_error.py",
    "e203_no_error.py",
    "e222_no_error.py",
    "e223_no_error.py",
    "e224_no_error.py",
    "e226_no_error.py",
    "e227_no_error.py",
    "e228_no_error.py",
    "e262_no_error.py",
    "e265_no_error.py",
    "e266_no_error.py",
    "e275_no_error.py",
    "e301_no_error.py",
    "e303_no_error.py",
    "e304_no_error.py",
]


class TestPycodestyleChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PycodestyleChecker
    CONFIG = {"pycodestyle_ignore": ["E24"]}

    @pytest.mark.parametrize("file_name, msg_id, line, col, desc", error_params)
    def test_error_cases(self, file_name, msg_id, line, col, desc):
        """Parameterized test that confirms various PEP8 errors are triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, file_name))
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=line,
                args=(msg_id, f"line {line}, column {col}: {desc}"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    @pytest.mark.parametrize("file_name", no_error_params)
    def test_no_error_cases(self, file_name):
        """Parameterized test that various PEP8 errors are not triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, file_name))
        with self.assertNoMessages():
            self.checker.process_module(mod)
