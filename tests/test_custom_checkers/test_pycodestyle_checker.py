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

    def test_error_e115(self) -> None:
        """Test that PEP8 error E115 (Expected an indented block) is triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e115_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=2,
                args=("E115", "line 2, column 0: expected an indented block (comment)"),
            )
        ):
            self.checker.process_module(mod)

    def test_no_error_e115(self) -> None:
        """Test that PEP8 error E115 (Expected an indented block) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e115_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e122(self) -> None:
        """Test that PEP8 error E122 (Continuation line missing indentation or outdented) is triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e122_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=2,
                args=(
                    "E122",
                    "line 2, column 0: continuation line missing indentation or outdented",
                ),
            )
        ):
            self.checker.process_module(mod)

    def test_no_error_e122(self) -> None:
        """Test that PEP8 error E122 (Continuation line missing indentation or outdented) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e122_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e127(self) -> None:
        """Test that PEP8 error E127 (Continuation line over-indented for visual indent) is triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e127_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=2,
                args=(
                    "E127",
                    "line 2, column 19: continuation line over-indented for visual indent",
                ),
            )
        ):
            self.checker.process_module(mod)

    def test_no_error_e127(self) -> None:
        """Test that PEP8 error E127 (Continuation line over-indented for visual indent) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e127_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e131(self) -> None:
        """Test that PEP8 error E131 (Continuation line unaligned for hanging indent) is triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e131_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=4,
                args=("E131", "line 4, column 8: continuation line unaligned for hanging indent"),
            )
        ):
            self.checker.process_module(mod)

    def test_no_error_e131(self) -> None:
        """Test that PEP8 error E131 (Continuation line unaligned for hanging indent) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e131_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e125(self) -> None:
        """Test that PEP8 error E125 (Continuation line with same indent as next logical line) is triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e125_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=2,
                args=(
                    "E125",
                    "line 2, column 4: continuation line with same indent as next logical line",
                ),
            )
        ):
            self.checker.process_module(mod)

    def test_no_error_e125(self) -> None:
        """Test that PEP8 error E125 (Continuation line with same indent as next logical line) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e125_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)

    def test_error_e129(self) -> None:
        """Test that PEP8 error E129 (Visually indented line with same indent as next logical line) is triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e129_error.py")
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="pep8-errors",
                line=4,
                args=(
                    "E129",
                    "line 4, column 4: visually indented line with same indent as next logical line",
                ),
            )
        ):
            self.checker.process_module(mod)

    def test_no_error_e129(self) -> None:
        """Test that PEP8 error E129 (Visually indented line with same indent as next logical line) is NOT triggered"""
        mod = MANAGER.ast_from_file(DIR_PATH + "e129_no_error.py")
        with self.assertNoMessages():
            self.checker.process_module(mod)
