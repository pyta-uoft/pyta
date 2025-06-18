import astroid
import pylint.testutils
from astroid import nodes

from python_ta.cfg.visitor import CFGVisitor
from python_ta.checkers.missing_return_checker import MissingReturnChecker
from python_ta.transforms.z3_visitor import Z3Visitor


class TestMissingReturnChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = MissingReturnChecker

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


class TestMissingReturnCheckerZ3Option(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = MissingReturnChecker
    CONFIG = {"z3": True}

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
            ),
            ignore_position=True,
        ):
            self.checker.visit_functiondef(func_node)
