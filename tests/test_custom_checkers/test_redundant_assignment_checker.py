import pylint.testutils
import astroid
from python_ta.checkers.redundant_assignment_checker import RedundantAssignmentChecker
from python_ta.cfg import CFGVisitor


class TestRedundantAssignmentChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = RedundantAssignmentChecker

    def setUp(self):
        self.setup_method()

    def test_no_messages_simple(self):
        src = """
        x = 10
        print(x)
        x = 10
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_1 = mod.nodes_of_class(astroid.Assign)

        with self.assertNoMessages():
            self.checker.visit_module(mod)
            self.checker.visit_assign(assign_1)

    def test_message_simple(self):
        src = """
        x = 10
        x = 230
        print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_1, _ = mod.nodes_of_class(astroid.Assign)

        self.checker.visit_module(mod)
        with self.assertAddsMessages(
            pylint.testutils.Message(
                msg_id='redundant-assignment',
                node=assign_1,
            ),
        ):
            self.checker.visit_assign(assign_1)

    def test_message_if_stmt(self):
        src = """
        x = 10
        y = 5
        if y > 5:
            x = 20
        else:
            x = 15
        print(x)
            
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_x, *_ = mod.nodes_of_class(astroid.Assign)

        self.checker.visit_module(mod)
        with self.assertAddsMessages(
            pylint.testutils.Message(
                msg_id='redundant-assignment',
                node=assign_x,
            ),
        ):
            self.checker.visit_assign(assign_x)

    def test_no_message_loop(self):
        src = """
        y = 5
        while y > 5:
            x = 10
            print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        _, assign_x, *_ = mod.nodes_of_class(astroid.Assign)
        self.checker.visit_module(mod)
        with self.assertNoMessages():
            self.checker.visit_assign(assign_x)

    def test_no_message_loop_(self):
        src = """
        y = 0
        for x in range(1, 10):
            x = 10
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        _, assign_x, *_ = mod.nodes_of_class(astroid.Assign)
        print(assign_x.as_string())

        self.checker.visit_module(mod)
        with self.assertNoMessages():
            self.checker.visit_assign(assign_x)

    def test_no_message_if_complex(self):
        src = """
        x = 10
        y = 5
        if y > 5:
            x = 20
        elif y > 50:
            x = 15
        else:
            pass
        print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_x, *_ = mod.nodes_of_class(astroid.Assign)

        self.checker.visit_module(mod)
        with self.assertNoMessages():
            self.checker.visit_assign(assign_x)
