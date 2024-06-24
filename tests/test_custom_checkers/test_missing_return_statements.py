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
        def no_return() -> None:
            print("no return")
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_correct_return(self):
        src = """
        def correct_return() -> int:
            return 1

        def correct_return_while() -> int:
            a = 10
            while a > 5:
                a -= 1
            return a

        def correct_return_for(lst: list[int]) -> int:
            for e in lst:
                e += 1
            return lst[0]
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node, func_node2, func_node3 = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_functiondef(func_node2)
            self.checker.visit_functiondef(func_node3)

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
                msg_id="missing-return-statement",
                node=func_node,
                args="missing_return",
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
                msg_id="missing-return-statement",
                node=func_node,
                args="missing_return_in_branch",
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
                msg_id="missing-return-statement",
                node=func_node,
                args="multiple_branches",
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
                msg_id="missing-return-statement",
                node=inner_func_node,
                args="inner_function",
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
                msg_id="missing-return-statement",
                node=func_node,
                args="try_except",
            ),
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func_node,
                args="try_except",
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_missing_return_with_while(self):
        src = """
        def while_loop() -> int:
            a = 10
            while a > 5:
                a -= 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func_node,
                args="while_loop",
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_missing_return_with_for(self):
        src = """
        def for_loop() -> int:
            for i in range(0, 10):
                print(i)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func_node,
                args="for_loop",
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)

    def test_no_return_annotations_not_missing(self):
        src = """
        def func1():
            print("no return")

        def func2():
            a = 1
            if a > 2:
                return
            print(a)

        def func3():
            if True:
                print("True")
            else:
                print("False")
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func1_node, func2_node, func3_node = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func1_node)
            self.checker.visit_functiondef(func2_node)
            self.checker.visit_functiondef(func3_node)

    def test_no_return_annotations_missing(self):
        src = """
        def func1():
            if True:
                print("no return")
            else:
                return 1

        def func2():
            a = 1
            while a > 0:
                if a > 2:
                    return a
                a -= 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func1_node, func2_node = mod.nodes_of_class(nodes.FunctionDef)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func1_node,
                args="func1",
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func1_node)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement", node=func2_node, args="func2"
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func2_node)
