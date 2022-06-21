import astroid
import pylint.testutils
from astroid import nodes
from python_ta.checkers.forbidden_io_function_checker import IOFunctionChecker


class TestForbiddenIOFunctionNoAllowedChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = IOFunctionChecker
    CONFIG = {}

    def setup(self):
        self.setup_method()

    def test_message_function_no_allowed(self):
        """No allowed functions, IO function input raises a message"""
        src = """
        def my_function(string: str):
            string = "hello"
            name = input()
            return name + string
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)
        with self.assertAddsMessages(
                pylint.testutils.MessageTest(msg_id="forbidden-IO-function", node=call,
                                             args=call.func.name),
                ignore_position=True,
        ):
            self.checker.visit_call(call)

    def test_message_class_no_allowed(self):
        """No allowed functions, IO function input raises a message"""
        src = """
        class Example:
            def my_function(self):
                name = input()
                return name
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)
        with self.assertAddsMessages(
                pylint.testutils.MessageTest(msg_id="forbidden-IO-function", node=call,
                                             args=call.func.name),
                ignore_position=True,
        ):
            self.checker.visit_call(call)


class TestForbiddenIOFunctionAllowedFunctionChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = IOFunctionChecker
    CONFIG = {"allowed_io": ["my_function"]}

    def test_no_message_function_allowed_function(self):
        """my_function is allowed, no messages will be raised for the use of input"""
        src = """
            def my_function(string: str):
                string = "hello"
                name = input()
                return name + string
            """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)

        with self.assertNoMessages():
            self.checker.visit_call(call)

    def test_message_class_allowed_function(self):
        """Only top-level function is allowed, function associated with a class will raise a
        message """
        src = """
        class Example:
            def my_function(self):
                name = input()
                return name
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)

        with self.assertAddsMessages(
                pylint.testutils.MessageTest(msg_id="forbidden-IO-function", node=call,
                                             args=call.func.name),
                ignore_position=True,
        ):
            self.checker.visit_call(call)


class TestForbiddenIOFunctionAllowedClassChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = IOFunctionChecker
    CONFIG = {"allowed_io": ["Example.my_function"]}

    def test_message_function_allowed_class(self):
        """Only my_function associated with a class is allowed, top-level function will raise a
        message """
        src = """
            def my_function(string: str):
                string = "hello"
                name = input()
                return name + string
            """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)

        with self.assertAddsMessages(
                pylint.testutils.MessageTest(msg_id="forbidden-IO-function", node=call,
                                             args=call.func.name),
                ignore_position=True,
        ):
            self.checker.visit_call(call)

    def test_no_message_class_allowed_class(self):
        """my_function associated with a class is allowed, no message is raised"""
        src = """
        class Example:
            def my_function(self):
                name = input()
                return name
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)

        with self.assertNoMessages():
            self.checker.visit_call(call)


if __name__ == "__main__":
    import pytest

    pytest.main(["test_forbidden_io_function_checker.py"])
