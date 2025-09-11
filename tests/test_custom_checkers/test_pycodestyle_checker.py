import os

import pylint.testutils
import pytest
from astroid.astroid_manager import MANAGER

from python_ta.checkers.pycodestyle_checker import PycodestyleChecker

DIR_PATH = os.path.normpath(
    os.path.join(__file__, "../../../examples/custom_checkers/e9989_pycodestyle/")
)

# Define parameter sets for different error and no-error tests
error_params = [
    ("E115", [(2, 0, "expected an indented block (comment)")]),
    ("E122", [(2, 0, "continuation line missing indentation or outdented")]),
    ("E123", [(3, 4, "closing bracket does not match indentation of opening bracket's line")]),
    ("E125", [(2, 4, "continuation line with same indent as next logical line")]),
    ("E127", [(2, 19, "continuation line over-indented for visual indent")]),
    ("E129", [(4, 4, "visually indented line with same indent as next logical line")]),
    ("E131", [(4, 8, "continuation line unaligned for hanging indent")]),
    ("E202", [(1, 19, "whitespace before ')'")]),
    ("E203", [(1, 30, "whitespace before ':'")]),
    ("E221", [(1, 5, "multiple spaces before operator")]),
    ("E222", [(1, 3, "multiple spaces after operator")]),
    ("E223", [(1, 1, "tab before operator")]),
    ("E224", [(1, 3, "tab after operator")]),
    ("E226", [(1, 5, "missing whitespace around arithmetic operator")]),
    ("E227", [(1, 5, "missing whitespace around bitwise or shift operator")]),
    ("E228", [(1, 5, "missing whitespace around modulo operator")]),
    ("E251", [(1, 7, "unexpected spaces around keyword / parameter equals")]),
    ("E261", [(1, 20, "at least two spaces before inline comment")]),
    (
        "E262",
        [
            (1, 7, "inline comment should start with '# '"),
            (2, 7, "inline comment should start with '# '"),
        ],
    ),
    ("E265", [(1, 0, "block comment should start with '# '")]),
    ("E266", [(1, 0, "too many leading '#' for block comment")]),
    ("E272", [(3, 8, "multiple spaces before keyword")]),
    ("E273", [(1, 3, "tab after keyword")]),
    ("E275", [(1, 16, "missing whitespace after keyword")]),
    ("E301", [(5, 4, "expected 1 blank line, found 0")]),
    ("E303", [(6, 0, "too many blank lines (3)")]),
    ("E304", [(12, 0, "blank lines found after function decorator")]),
    (
        "E305",
        [
            (4, 0, "expected 2 blank lines after class or function definition, found 0"),
            (9, 0, "expected 2 blank lines after class or function definition, found 0"),
        ],
    ),
]


class TestPycodestyleChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PycodestyleChecker
    CONFIG = {"pycodestyle_ignore": ["E24"]}

    @pytest.mark.parametrize("msg_id, args", error_params)
    def test_error_cases(self, msg_id, args):
        """Parameterized test that confirms various PEP8 errors are triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, msg_id.lower() + "_error.py"))
        with self.assertAddsMessages(
            *[
                pylint.testutils.MessageTest(
                    msg_id="pep8-errors",
                    line=line,
                    args=(msg_id, f"line {line}, column {col}: {desc}"),
                )
                for line, col, desc in args
            ],
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    @pytest.mark.parametrize("msg_id", error_params)
    def test_no_error_cases(self, msg_id):
        """Parameterized test that various PEP8 errors are not triggered"""
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, msg_id[0].lower() + "_no_error.py"))
        with self.assertNoMessages():
            self.checker.process_module(mod)
