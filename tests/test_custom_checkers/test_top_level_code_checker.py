import astroid
import pylint.testutils

from python_ta.checkers.top_level_code_checker import TopLevelCodeChecker


class TestTopLevelCodeChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = TopLevelCodeChecker
    CONFIG = {}

    def test_message_simple(self):
        """Top level code not allowed, raises a message."""
        src = """
        print("testing code")
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[0], args=2
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    def test_message_complex(self):
        """Top level code not allowed, raises a message."""
        src = """
        if __name__ == "__main__":
            print("I'm in main")
        print("testing code")
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[1], args=4
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    def test_no_message_import(self):
        """Top level import allowed, no message."""
        src = """
        import test
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_no_message_import_from(self):
        """Top level import from allowed, no message."""
        src = """
        from test import unittest
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_no_message_function_def(self):
        """Top level function allowed, no message."""
        src = """
        def print_hello():
            print("hello")
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_no_message_class_def(self):
        """Top level class allowed, no message."""
        src = """
        class Printer:
            def print_hello():
                print("hello")
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_no_message_constant_assignment(self):
        """Top level constant assignment allowed, no message."""
        src = """
        MAX_DURATION = 30
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_message_annotated_assignment(self):
        """Top level regular assignment with annotation not allowed, raises a message."""
        src = """
        max_num: int = 30
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[0], args=2
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    def test_no_message_annotated_constant_assignment(self):
        """Top level constant assignment with annotation allowed, no message."""
        src = """
        MAX_DURATION: int = 30
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_message_regular_assignment(self):
        """Top level regular assignment not allowed, raises a message."""
        src = """
        name = "George"
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[0], args=2
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    def test_no_message_type_alias_assignment(self):
        """Top level type alias assignment allowed, no message."""
        src = """
        MyType = list[list[list[int]]]
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_message_type_alias_assignment(self):
        """Top level type alias assignment not allowed, raises a message."""
        src = """
        TypeName = list[int]
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[0], args=2
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    def test_message_regular_assignment_unpacking(self):
        """Top level regular unpacking assignment not allowed, raises a message."""
        src = """
        name, CONST = "George", 3
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[0], args=2
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    def test_message_regular_assignment_starred(self):
        """Top level regular assignment with a starred target not allowed, raises a message."""
        src = """
        NAME, *nums = ["George", 3, 4]
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[0], args=2
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)

    def test_no_message_is_main(self):
        """Top level code in main block is allowed, no message."""
        src = """
        if __name__ == "__main__":
            print("I'm in main")
        """
        mod = astroid.parse(src)
        with self.assertNoMessages():
            self.checker.visit_module(mod)

    def test_message_attribute_assignment(self):
        """Top level code to assign attributes not allowed, raises a message."""
        src = """
        class X:
            a = 5
        Y = X()
        Y.a = 6
        """
        mod = astroid.parse(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-top-level-code", node=mod.body[2], args=5
            ),
            ignore_position=True,
        ):
            self.checker.visit_module(mod)
