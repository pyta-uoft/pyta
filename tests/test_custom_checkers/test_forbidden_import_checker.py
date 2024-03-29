import os

import astroid
import pylint.testutils

from python_ta.checkers.forbidden_import_checker import ForbiddenImportChecker


class TestForbiddenImportChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = ForbiddenImportChecker
    CONFIG = {
        "allowed_import_modules": ["python_ta"],
        "extra_imports": ["datetime", "math.floor"],
    }

    def test_forbidden_import_statement(self) -> None:
        """Tests for `import XX` statements"""
        src = """
        import copy
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.Import)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-import", node=node, line=1, args=("module copy",)
            ),
            ignore_position=True,
        ):
            self.checker.visit_import(node)

    def test_forbidden_import_from(self) -> None:
        """Tests for `from XX import XX` statements"""
        src = """
        from sys import path
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.ImportFrom)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-import", node=node, line=1, args=("path from module sys",)
            ),
            ignore_position=True,
        ):
            self.checker.visit_importfrom(node)

    def test_allowed_import_statement(self) -> None:
        """Tests for `import XX` statements"""
        src = """
        import python_ta
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.Import)

        with self.assertNoMessages():
            self.checker.visit_import(node)

    def test_extra_import_statement(self) -> None:
        src = """
        import datetime
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.Import)

        with self.assertNoMessages():
            self.checker.visit_import(node)

    def test_forbidden_dunder_import(self) -> None:
        src = """
        __import__('math')
        """
        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.Call)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-import", node=node, line=1, args=("module math",)
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(node)

    @pylint.testutils.set_config(allow_local_imports=True)
    def test_allowed_local_import(self) -> None:
        src = """
        import imported_module
        """

        self.linter.current_file = os.path.abspath(__file__ + "/../test_e9999_local_import/main.py")

        mod = astroid.parse(src)
        node, *_ = mod.nodes_of_class(astroid.nodes.Import)

        with self.assertNoMessages():
            self.checker.visit_import(node)

    def test_disallowed_local_import(self) -> None:
        src = """
        import imported_module
        """

        self.linter.current_file = os.path.abspath(__file__ + "/../test_e9999_local_import/main.py")

        mod = astroid.parse(src)
        node, *_ = mod.nodes_of_class(astroid.nodes.Import)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-import", node=node, line=1, args=("module imported_module",)
            ),
            ignore_position=True,
        ):
            self.checker.visit_import(node)

    def test_allowed_function_import(self) -> None:
        src = """
        from math import floor
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.ImportFrom)

        with self.assertNoMessages():
            self.checker.visit_importfrom(node)

    def test_multiple_disallowed_function_import(self) -> None:
        src = """
        from math import sqrt, ceil
        """

        mod = astroid.parse(src)

        node, *_ = mod.nodes_of_class(astroid.nodes.ImportFrom)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-import", node=node, line=1, args=("sqrt, ceil from module math",)
            ),
            ignore_position=True,
        ):
            self.checker.visit_importfrom(node)
