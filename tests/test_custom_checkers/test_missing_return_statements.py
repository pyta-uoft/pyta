import astroid
import pylint.testutils
from astroid import nodes

from python_ta.cfg.visitor import CFGVisitor
from python_ta.checkers.inconsistent_or_missing_returns_checker import (
    InconsistentReturnChecker,
)
from python_ta.transforms.z3_visitor import Z3Visitor


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
                line=3,
                end_line=3,
                col_offset=0,
                end_col_offset=18,
            ),
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
                line=4,
                end_line=7,
                col_offset=0,
                end_col_offset=28,
            ),
        ):
            self.checker.visit_functiondef(func_node)

    def test_missing_return_with_multiple_branches(self):
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
                line=5,
                end_line=8,
                col_offset=0,
                end_col_offset=21,
            ),
        ):
            self.checker.visit_functiondef(func_node)

    def test_missing_return_with_nested_functions(self):
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
                line=4,
                end_line=4,
                col_offset=4,
                end_col_offset=22,
            ),
        ):
            self.checker.visit_functiondef(outer_func_node)
            self.checker.visit_functiondef(inner_func_node)

    def test_missing_return_with_try_except(self):
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
                line=6,
                end_line=6,
                col_offset=0,
                end_col_offset=14,
            ),
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func_node,
                args="try_except",
                line=4,
                end_line=4,
                col_offset=0,
                end_col_offset=14,
            ),
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
                line=4,
                end_line=5,
                col_offset=0,
                end_col_offset=14,
            ),
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
                line=3,
                end_line=4,
                col_offset=0,
                end_col_offset=12,
            ),
        ):
            self.checker.visit_functiondef(func_node)

    def test_correct_return_no_return_annotations(self):
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

    def test_missing_return_no_return_annotations(self):
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
                line=3,
                end_line=6,
                col_offset=0,
                end_col_offset=9,
            ),
        ):
            self.checker.visit_functiondef(func1_node)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func2_node,
                args="func2",
                line=10,
                end_line=13,
                col_offset=0,
                end_col_offset=9,
            ),
        ):
            self.checker.visit_functiondef(func2_node)

    def test_correct_return_raise_statement(self):
        src = """
        def division(x, y) -> int:
            if y == 0:
                raise Exception
            else:
                return x / y
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)

    def test_missing_return_raise_statement(self):
        src = """
        def division_missing_return(x, y) -> int:
            if y == 0:
                raise Exception
            elif x > y:
                return x / y
        """

        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func_node,
                args="division_missing_return",
                line=5,
                end_line=6,
                col_offset=0,
                end_col_offset=27,
            ),
        ):
            self.checker.visit_functiondef(func_node)

    def test_z3_unfeasible_missing_return(self):
        src = """
        def unfeasible_missing_return(x: str) -> str:
            '''
            Preconditions:
                - x[0:2] == "ab"
            '''
            if x in "cd":
                print("empty string")
            else:
                return x
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertNoMessages():
            self.checker.linter.config.z3 = True
            self.checker.visit_functiondef(func_node)

    def test_z3_partially_feasible_missing_return(self):
        src = """
        def feasible_missing_return(x: int) -> int:
            '''
            Preconditions:
                - x in [1, 2, 3, 4, 5]
            '''
            if x > 5:
                print(x)
            print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func_node,
                args="feasible_missing_return",
                line=9,
                end_line=9,
                col_offset=0,
                end_col_offset=27,
            ),
        ):
            self.checker.linter.config.z3 = True
            self.checker.visit_functiondef(func_node)

    def test_z3_feasible_missing_return(self):
        src = """
        def feasible_missing_return(x: bool, y: int) -> int:
            '''
            Preconditions:
                - x
                - y > 5
            '''
            while not x:
                print(1)
                y += 1
                if y > 10:
                    return y
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        func_node = next(mod.nodes_of_class(nodes.FunctionDef))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="missing-return-statement",
                node=func_node,
                args="feasible_missing_return",
                line=8,
                end_line=12,
                col_offset=0,
                end_col_offset=27,
            ),
        ):
            self.checker.linter.config.z3 = True
            self.checker.visit_functiondef(func_node)
