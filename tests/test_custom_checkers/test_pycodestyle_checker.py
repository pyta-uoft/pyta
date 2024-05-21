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

    def test_error_e222(self) -> None:
        """Test that PEP8 error E222 (multiple spaces after operator) triggers"""
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
        """Test that PEP8 error E222 (multiple spaces after operator) is not triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e222_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e223(self) -> None:
        """Test that PEP8 error E223 (tab before operator) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e223_error.py")
        args = ("E223", "line 1, column 1: tab before operator")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-errors", line=1, node=None, args=args),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e223(self) -> None:
        """Test that PEP8 error E223 (tab before operator) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e223_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e224(self) -> None:
        """Test that PEP8 error E224 (tab after operator) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e224_error.py")
        args = ("E224", "line 1, column 3: tab after operator")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-errors", line=1, node=None, args=args),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e224(self) -> None:
        """Test that PEP8 error E224 (tab after operator) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e224_no_error.py")
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

    def test_error_e227(self) -> None:
        """Test that PEP8 error E227 (missing whitespace around bitwise or shift operator) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e227_error.py")
        args = ("E227", "line 1, column 5: missing whitespace around bitwise or shift operator")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-errors", line=1, node=None, args=args),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e227(self) -> None:
        """Test that PEP8 error E227 (missing whitespace around bitwise or shift operator) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e227_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e228(self) -> None:
        """Test that PEP8 error E228 (missing whitespace around modulo operator) triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e228_error.py")
        args = ("E228", "line 1, column 5: missing whitespace around modulo operator")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-errors", line=1, node=None, args=args),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e228(self) -> None:
        """Test that PEP8 error E228 (missing whitespace around modulo operator) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e228_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e262(self) -> None:
        """Test that PEP8 error E262 (inline comment should start with '# ') triggers"""
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
        """Test that PEP8 error E262 (inline comment should start with '# ') is not triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e262_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e265(self) -> None:
        """Test that PEP8 error E265 (block comment should start with '# ') triggers"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e265_error.py")
        args = ("E265", "line 1, column 0: block comment should start with '# '")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="pep8-errors", line=1, node=None, args=args),
            ignore_position=True,
        ):
            self.checker.process_module(mod)

    def test_no_error_e265(self) -> None:
        """Test that PEP8 error E265 (block comment should start with '# ') is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e265_no_error.py")
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
                line=5,
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
