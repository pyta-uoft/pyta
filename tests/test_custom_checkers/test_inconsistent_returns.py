import astroid
import pylint.testutils
from astroid import nodes

from python_ta.cfg.visitor import CFGVisitor
from python_ta.checkers.inconsistent_or_missing_returns_checker import (
    InconsistentReturnChecker,
)


class TestInconsistentReturnChecker(pylint.testutils.CheckerTestCase):
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

    def test_consistent_return(self):
        src = """
        def consistent_return() -> int:
            if True:
                return 1
            else:
                return 0
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_inconsistent_return(self):
        src = """
            def inconsistent_return() -> int:
                a = 1
                if a > 2:
                    return 2
                return
            """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))
        _, inconsistent_return_node = mod.nodes_of_class(nodes.Return)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="inconsistent-returns",
                node=inconsistent_return_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_nested_inconsistent_returns(self):
        src = """
        def nested_inconsistent_returns() -> int:
            def inner_func():
                if True:
                    return 1
            if False:
                return inner_func()
            return
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))
        _, _, inconsistent_return_node = mod.nodes_of_class(nodes.Return)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="inconsistent-returns",
                node=inconsistent_return_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_try_except_inconsistent(self):
        src = """
        def try_except_finally_inconsistent() -> int:
            try:
                return 1
            except Exception:
                return
            finally:
                print("done")
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))
        _, inconsistent_return_node = mod.nodes_of_class(nodes.Return)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="inconsistent-returns",
                node=inconsistent_return_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)
