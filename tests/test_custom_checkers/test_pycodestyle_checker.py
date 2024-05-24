import os

import pylint.testutils
import pytest
from astroid.astroid_manager import MANAGER

from python_ta.checkers.pycodestyle_checker import PycodestyleChecker

DIR_PATH = os.path.join(__file__, "../../../examples/custom_checkers/e9989_pycodestyle/")


def pytest_generate_tests(metafunc):
    # called once per each test function
    funcarglist = metafunc.cls.params.get(metafunc.function.__name__, [])
    argnames = sorted(funcarglist[0]) if funcarglist else []
    metafunc.parametrize(
        argnames, [[funcargs[name] for name in argnames] for funcargs in funcarglist]
    )


class TestPycodestyleChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PycodestyleChecker
    CONFIG = {"pycodestyle_ignore": ["E24"]}

    params = {
        "test_error_e123": [dict(filename="e123_error.py", should_raise=True)],
        "test_no_error_e123": [dict(filename="e123_no_error.py", should_raise=False)],
        "test_error_e203": [dict(filename="e203_error.py", should_raise=True)],
        "test_no_error_e203": [dict(filename="e203_no_error.py", should_raise=False)],
        "test_error_e222": [dict(filename="e222_error.py", should_raise=True)],
        "test_no_error_e222": [dict(filename="e222_no_error.py", should_raise=False)],
        "test_error_e223": [dict(filename="e223_error.py", should_raise=True)],
        "test_no_error_e223": [dict(filename="e223_no_error.py", should_raise=False)],
        "test_error_e224": [dict(filename="e224_error.py", should_raise=True)],
        "test_no_error_e224": [dict(filename="e224_no_error.py", should_raise=False)],
        "test_error_e226": [dict(filename="e226_error.py", should_raise=True)],
        "test_no_error_e226": [dict(filename="e226_no_error.py", should_raise=False)],
        "test_error_e227": [dict(filename="e227_error.py", should_raise=True)],
        "test_no_error_e227": [dict(filename="e227_no_error.py", should_raise=False)],
        "test_error_e228": [dict(filename="e228_error.py", should_raise=True)],
        "test_no_error_e228": [dict(filename="e228_no_error.py", should_raise=False)],
        "test_error_e262": [dict(filename="e262_error.py", should_raise=True)],
        "test_no_error_e262": [dict(filename="e262_no_error.py", should_raise=False)],
        "test_error_e265": [dict(filename="e265_error.py", should_raise=True)],
        "test_no_error_e265": [dict(filename="e265_no_error.py", should_raise=False)],
    }

    def run_test(self, filename, should_raise, msg_args=None):
        mod = MANAGER.ast_from_file(os.path.join(DIR_PATH, filename))
        if should_raise:
            with self.assertAddsMessages(
                pylint.testutils.MessageTest(
                    msg_id="pep8-errors",
                    line=msg_args["line"],
                    node=None,
                    args=(msg_args["code"], msg_args["message"]),
                ),
                ignore_position=True,
            ):
                self.checker.process_module(mod)
        else:
            with self.assertNoMessages():
                self.checker.process_module(mod)

    def test_error_e123(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 3,
                "code": "E123",
                "message": "line 3, column 4: closing bracket does not match indentation of opening bracket's line",
            },
        )

    def test_no_error_e123(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e203(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E203",
                "message": "line 1, column 30: whitespace before ':'",
            },
        )

    def test_no_error_e203(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e222(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E222",
                "message": "line 1, column 3: multiple spaces after operator",
            },
        )

    def test_no_error_e222(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e223(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E223",
                "message": "line 1, column 1: tab before operator",
            },
        )

    def test_no_error_e223(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e224(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E224",
                "message": "line 1, column 3: tab after operator",
            },
        )

    def test_no_error_e224(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e226(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E226",
                "message": "line 1, column 5: missing whitespace around arithmetic operator",
            },
        )

    def test_no_error_e226(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e227(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E227",
                "message": "line 1, column 5: missing whitespace around bitwise or shift operator",
            },
        )

    def test_no_error_e227(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e228(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E228",
                "message": "line 1, column 5: missing whitespace around modulo operator",
            },
        )

    def test_no_error_e228(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e262(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E262",
                "message": "line 1, column 7: inline comment should start with '# '",
            },
        )

    def test_no_error_e262(self, filename, should_raise):
        self.run_test(filename, should_raise)

    def test_error_e265(self, filename, should_raise):
        self.run_test(
            filename,
            should_raise,
            msg_args={
                "line": 1,
                "code": "E265",
                "message": "line 1, column 0: block comment should start with '# '",
            },
        )

    def test_no_error_e265(self, filename, should_raise):
        self.run_test(filename, should_raise)
