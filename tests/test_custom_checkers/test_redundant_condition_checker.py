import astroid
import pylint.testutils
from astroid import nodes

from python_ta.cfg import CFGVisitor
from python_ta.checkers.redundant_condition_checker import RedundantConditionChecker
from python_ta.transforms.z3_visitor import Z3Visitor


class TestRedundantConditionChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = RedundantConditionChecker
    CONFIG = {"z3": True}

    def test_redundant_by_precondition(self):
        src = """
        def func(x: int):
            '''
            Preconditions:
                - x > 10
            '''
            if x > 5:
                print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        condition_node, *_ = mod.nodes_of_class(nodes.If)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="redundant-condition", node=condition_node),
            ignore_position=True,
        ):
            self.checker.visit_if(condition_node)

    def test_redundant_by_if_condition(self):
        src = """
        def func(x: int):
            if x > 5:
                if x > 3:
                    print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        *_, condition_node = mod.nodes_of_class(nodes.If)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="redundant-condition", node=condition_node),
            ignore_position=True,
        ):
            self.checker.visit_if(condition_node)

    def test_redundant_by_while_condition(self):
        src = """
        def func(x: int):
            '''
            Preconditions:
                - x > 10
            '''
            while x > 0:
                if x != 0:
                    print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        condition_node, *_ = mod.nodes_of_class(nodes.If)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(msg_id="redundant-condition", node=condition_node),
            ignore_position=True,
        ):
            self.checker.visit_if(condition_node)

    def test_not_redundant_condition(self):
        src = """
        def func(x: str):
            '''
            Preconditions:
                - x[0:2] == "ab"
            '''
            if x != "abc":
                print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        condition_node, *_ = mod.nodes_of_class(nodes.If)

        with self.assertNoMessages():
            self.checker.visit_if(condition_node)

    def test_partially_redundant_condition(self):
        src = """
        def func(x: int):
            '''
            Preconditions:
                - x > 10
            '''
            if x > 10 and x < 15:
                print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        condition_node, *_ = mod.nodes_of_class(nodes.If)

        with self.assertNoMessages():
            self.checker.visit_if(condition_node)

    def test_redundant_condition_partial_paths(self):
        src = """
        def func(x: int, y: bool):
            '''
            Preconditions:
                - x > 10
            '''
            if not y:
                x = -1
            if x > 0:
                print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        condition_node, *_ = mod.nodes_of_class(nodes.If)

        with self.assertNoMessages():
            self.checker.visit_if(condition_node)

    def test_not_redundant_by_reassignment(self):
        src = """
        def func(x: float):
            '''
            Preconditions:
                - x in [1.0, 2.0]
            '''
            x = None
            if x == 1.0 or x == 2.0:
                print(x)
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        condition_node, *_ = mod.nodes_of_class(nodes.If)

        with self.assertNoMessages():
            self.checker.visit_if(condition_node)


# inspiration: check if the reassigned variable has the same type as previous one
# if yes, update the variable value in Z3Environment and continue using it in CFG traverse
