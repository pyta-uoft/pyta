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
    # ("E101", [(3, 0, "indentation contains mixed spaces and tabs")]),
    ("E115", [(2, 0, "expected an indented block (comment)")]),
    ("E116", [(1, 8, "unexpected indentation (comment)")]),
    ("E122", [(2, 0, "continuation line missing indentation or outdented")]),
    ("E123", [(3, 4, "closing bracket does not match indentation of opening bracket's line")]),
    ("E124", [(3, 8, "closing bracket does not match visual indentation")]),
    ("E125", [(2, 4, "continuation line with same indent as next logical line")]),
    ("E127", [(2, 19, "continuation line over-indented for visual indent")]),
    ("E128", [(2, 8, "continuation line under-indented for visual indent")]),
    ("E129", [(4, 4, "visually indented line with same indent as next logical line")]),
    ("E131", [(4, 8, "continuation line unaligned for hanging indent")]),
    ("E201", [(1, 6, "whitespace after '('")]),
    ("E202", [(1, 19, "whitespace before ')'")]),
    ("E203", [(1, 30, "whitespace before ':'")]),
    ("E204", [(1, 1, "whitespace after decorator '@'"), (6, 1, "whitespace after decorator '@'")]),
    ("E211", [(1, 14, "whitespace before '('")]),
    ("E221", [(1, 5, "multiple spaces before operator")]),
    ("E222", [(1, 3, "multiple spaces after operator")]),
    ("E223", [(1, 1, "tab before operator")]),
    ("E224", [(1, 3, "tab after operator")]),
    (
        "E225",
        [
            (2, 4, "missing whitespace around operator"),
            (5, 4, "missing whitespace around operator"),
            (8, 4, "missing whitespace around operator"),
            (8, 12, "missing whitespace around operator"),
            (8, 20, "missing whitespace around operator"),
            (11, 2, "missing whitespace around operator"),
            (13, 1, "missing whitespace around operator"),
            (15, 1, "missing whitespace around operator"),
            (17, 1, "missing whitespace around operator"),
            (19, 1, "missing whitespace around operator"),
        ],
    ),
    (
        "E226",
        [
            (1, 5, "missing whitespace around arithmetic operator"),
            (3, 5, "missing whitespace around arithmetic operator"),
        ],
    ),
    ("E227", [(1, 5, "missing whitespace around bitwise or shift operator")]),
    ("E228", [(1, 5, "missing whitespace around modulo operator")]),
    ("E231", [(2, 13, "missing whitespace after ','")]),
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
    ("E271", [(3, 11, "multiple spaces after keyword")]),
    ("E272", [(3, 8, "multiple spaces before keyword")]),
    ("E273", [(1, 3, "tab after keyword")]),
    ("E274", [(1, 6, "tab before keyword")]),
    ("E275", [(1, 16, "missing whitespace after keyword")]),
    ("E301", [(5, 4, "expected 1 blank line, found 0")]),
    ("E302", [(3, 0, "expected 2 blank lines, found 0")]),
    ("E303", [(6, 0, "too many blank lines (3)")]),
    ("E304", [(12, 0, "blank lines found after function decorator")]),
    (
        "E305",
        [
            (4, 0, "expected 2 blank lines after class or function definition, found 0"),
            (9, 0, "expected 2 blank lines after class or function definition, found 0"),
        ],
    ),
    ("E306", [(3, 4, "expected 1 blank line before a nested definition, found 0")]),
    ("E502", [(2, 14, "the backslash is redundant between brackets")]),
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
                    args=(f"{desc}", msg_id),
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

    def test_e101_error(self):
        """
        Test case for PEP8 error E101 indentation contains mixed spaces and tabs

        This test is separate from test_error_cases() to handle the W191 message that is
        always emitted alongside E101.
        """
        expected = [
            ("E101", 3, 0, "indentation contains mixed spaces and tabs"),
            ("W191", 3, 0, "indentation contains tabs"),
        ]
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e101_error.py"))
        with self.assertAddsMessages(
            *[
                pylint.testutils.MessageTest(
                    msg_id="pep8-errors",
                    line=line,
                    args=(desc, msg_id),
                )
                for msg_id, line, col, desc in expected
            ],
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_e101_no_error(self):
        """
        Tests that PEP8 error E101 is not triggered.
        This test is separate due to the same issue as noted in test_e101_error().
        """
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, "e101_no_error.py"))
        with self.assertNoMessages():
            self.checker.process_module(mod)
