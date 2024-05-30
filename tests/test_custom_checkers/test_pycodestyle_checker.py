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

    def test_error_e266(self) -> None:
        """Test that PEP8 error E266 (too many leading '#' for block comment) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e266_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=1,
                node=None,
                args=("E266", "line 1, column 0: too many leading '#' for block comment"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e266(self) -> None:
        """Test that PEP8 error E266 (too many leading '#' for block comment) is not triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e266_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e275(self) -> None:
        """Test that PEP8 error E275 (missing whitespace after keyword) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e275_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=1,
                node=None,
                args=("E275", "line 1, column 16: missing whitespace after keyword"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e275(self) -> None:
        """Test that PEP8 error E275 (missing whitespace after keyword) is not triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e275_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e301(self) -> None:
        """Test that PEP8 error E301 (expected 1 blank line, found 0) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e301_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=6,
                node=None,
                args=("E301", "line 5, column 4: expected 1 blank line, found 0"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e301(self) -> None:
        """Test that PEP8 error E301 (expected 1 blank line, found 0) is not triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e301_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e303(self) -> None:
        """Test that PEP8 error E303 (Too many blank lines (3)) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e303_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=6,
                node=None,
                args=("E303", "line 6, column 0: too many blank lines (3)"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e303(self) -> None:
        """Test that PEP8 error E303 (too many blank lines (3)) is not triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e303_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e304(self) -> None:
        """Test that PEP8 error E304 (Blank line found after function decorator) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e304_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=12,
                node=None,
                args=("E304", "line 12, column 0: blank lines found after function decorator"),
            ),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e304(self) -> None:
        """Test that PEP8 error E304 (Blank line found after function decorator) is not triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e304_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)
