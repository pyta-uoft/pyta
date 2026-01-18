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
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call, args=call.func.name
            ),
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
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call, args=call.func.name
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call)

    def test_message_global(self):
        """Global scope not allowed, IO function input raises a message"""
        src = """
        name = input()
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call, args=call.func.name
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call)

    def test_message_alias(self):
        """Calling an alias of a forbidden IO function raises a message"""
        src = """
        alias = input
        alias()
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="forbidden-IO-function", node=call, args="input"),
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
        message"""
        src = """
        class Example:
            def my_function(self):
                name = input()
                return name
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call, args=call.func.name
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call)


class TestForbiddenIOFunctionAllowedClassChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = IOFunctionChecker
    CONFIG = {"allowed_io": ["Example.my_function"]}

    def test_message_function_allowed_class(self):
        """Only my_function associated with a class is allowed, top-level function will raise a
        message"""
        src = """
            def my_function(string: str):
                string = "hello"
                name = input()
                return name + string
            """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call, args=call.func.name
            ),
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

    def test_message_global_allowed_main_block(self):
        """Main block is allowed, IO function input does not raises a message"""
        src = """
        if __name__ == "__main__":
            name = input()
        """
        mod = astroid.parse(src)
        call, *_ = mod.nodes_of_class(nodes.Call)

        with self.assertNoMessages():
            self.checker.visit_call(call)


class TestForbiddenIOFunctionForbiddenMethod(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = IOFunctionChecker
    CONFIG = {"forbidden_io_functions": ["A.func", "A.B.func", "func"]}

    def test_message_method(self):
        """A.func method not allowed, IO function input raises a message"""
        src = """
        class A:
            def func(self):
                pass

        instance = A()
        instance.func() #@
        """
        call_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call_node, args="A.func"
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call_node)

    def test_message_method_nested_class(self):
        """A.B.func method not allowed, IO function input raises a message"""
        src = """
        class A:
            class B:
                def func(self):
                    pass

        instance = A.B()
        instance.func() #@
        """
        call_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call_node, args="A.B.func"
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call_node)

    def test_message_method_non_qualified_name(self):
        """func is not a valid identifier for C.func, no message raised"""
        src = """
        class C:
            def func(self):
                pass

        instance = C()
        instance.func() #@
        """
        call_node = astroid.extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_call(call_node)

    def test_message_method_alias(self):
        """Alias of a method that is not allowed, message should be raised"""
        src = """
        class A:
            def func(self):
                pass

        instance = A()
        alias = instance.func
        alias() #@
        """
        call_node = astroid.extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call_node, args="A.func"
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call_node)


class TestForbiddenIOFunctionForbiddenImport(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = IOFunctionChecker
    CONFIG = {"forbidden_io_functions": ["A.func", "top_level"]}

    def test_message_imported_method(self):
        """A.func is forbidden, despite being imported, message should be raised"""
        src = """
        from imported_module import A

        instantiated = A()
        instantiated.func()
        """

        imported_module_src = """
        class A:
            def func(self):
                pass
        """

        mod = astroid.parse(src)
        imported_module = astroid.parse(imported_module_src, "imported_module")
        mod["imported_module"] = imported_module

        _, call_node = mod.nodes_of_class(nodes.Call)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call_node, args="A.func"
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call_node)

    def test_message_func(self):
        """top_level is forbidden, message should be raised"""
        src = """
        from imported_module import top_level

        top_level()
        """

        imported_module_src = """
        def top_level():
            pass
        """

        mod = astroid.parse(src)
        imported_module = astroid.parse(imported_module_src, "imported_module")
        mod["imported_module"] = imported_module

        call_node, *_ = mod.nodes_of_class(nodes.Call)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="forbidden-IO-function", node=call_node, args="top_level"
            ),
            ignore_position=True,
        ):
            self.checker.visit_call(call_node)


if __name__ == "__main__":
    import pytest

    pytest.main(["test_forbidden_io_function_checker.py"])
