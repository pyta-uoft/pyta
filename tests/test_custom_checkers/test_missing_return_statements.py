import astroid
import pylint.testutils
from astroid import nodes

from python_ta.cfg.visitor import CFGVisitor
from python_ta.checkers.inconsistent_or_missing_returns_checker import (
    InconsistentReturnChecker,
)


class TestMissingReturnChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = InconsistentReturnChecker

    def test_ignore_none_return(self):
        src = """
                def test():
                    print("no return")

                def test2() -> None:
                    print("no return")
                """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node, func_node2 = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_functiondef(func_node2)

    def test_missing_return(self):
        src = """
            def missing_return() -> int:
                print("no return")
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statements",
                node=func_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_missing_return_in_branch(self):
        src = """
        def missing_return_in_branch() -> int:
            a = 1
            if a > 3:
                print("no return")
            else:
                return a
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statements",
                node=func_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_function_with_multiple_branches(self):
        src = """
        def multiple_branches() -> int:
            if False:
                return 1
            elif True:
                print("no return")
            else:
                return 2
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statements",
                node=func_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_function_with_nested_functions(self):
        src = """
        def outer_function():
            def inner_function() -> int:
                print("inner function")
            print("no return")
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        outer_func_node, inner_func_node = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statements",
                node=inner_func_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(outer_func_node)
            self.checker.visit_functiondef(inner_func_node)

    def test_function_with_try_except(self):
        src = """
        def try_except() -> int:
            try:
                print("try block")
            except Exception:
                print("except block")
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statements",
                node=func_node,
            ),
            pylint.testutils.MessageTest(
                msg_id="missing-return-statements",
                node=func_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)
