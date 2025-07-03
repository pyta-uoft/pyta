import astroid
import pylint.testutils
import pytest

from python_ta.checkers.top_level_code_checker import TopLevelCodeChecker


class TestTopLevelCodeChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = TopLevelCodeChecker
    CONFIG = {}

    @pytest.mark.parametrize(
        "src, lineno",
        [
            (
                """
                print("testing code")
                """,
                2,
            ),
            (
                """
                if __name__ == "__main__":
                    print("I'm in main")
                print("testing code")
                """,
                4,
            ),
            (
                """
                max_num: int = 30
                """,
                2,
            ),
            (
                """
                name = "George"
                """,
                2,
            ),
            (
                """
                TypeName = list[int]
                """,
                2,
            ),
            (
                """
                name, CONST = "George", 3
                """,
                2,
            ),
            (
                """
                NAME, *nums = ["George", 3, 4]
                """,
                2,
            ),
            (
                """
                class X:
                    a = 5
                Y = X()
                Y.a = 6
                """,
                5,
            ),
        ],
        ids=[
            "message_simple",
            "message_complex",
            "message_annotated_assignment",
            "message_regular_assignment",
            "message_type_alias_assignment",
            "message_regular_assignment_unpacking",
            "message_regular_assignment_starred",
            "message_attribute_assignment",
        ],
    )
    def test_forbidden_top_level_code(self, src, lineno):
        """
        Cases that must raise forbidden-top-level-code.
        Assumes that the last statement in the body is the node associated with the error, unless the code contains `Y.a`
        """
        mod = astroid.parse(src)
        if "Y.a" in src:
            node = mod.body[2]
        else:
            node = mod.body[-1]

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="forbidden-top-level-code", node=node, args=lineno),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    @pytest.mark.parametrize(
        "src",
        [
            """
            import test
            """,
            """
            from test import unittest
            """,
            """
            def print_hello():
                print("hello")
            """,
            """
            class Printer:
                def print_hello():
                    print("hello")
            """,
            """
            MAX_DURATION = 30
            """,
            """
            MAX_DURATION: int = 30
            """,
            """
            MyType = list[list[list[int]]]
            """,
            """
            if __name__ == "__main__":
                print("I'm in main")
            """,
        ],
        ids=[
            "no_message_import",
            "no_message_import_from",
            "no_message_function_def",
            "no_message_class_def",
            "no_message_constant_assignment",
            "no_message_annotated_constant_assignment",
            "no_message_type_alias_assignment",
            "no_message_is_main",
        ],
    )
    def test_allowed_top_level_code(self, src):
        """Cases that must NOT raise forbidden-top-level-code"""
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)
