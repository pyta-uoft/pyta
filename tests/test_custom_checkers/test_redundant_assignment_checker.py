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
        assign_1, *_ = mod.nodes_of_class(astroid.Assign)

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

    def test_message_loop_complex(self):
        src = """
        y = 0
        x = 10
        for y in range(1, 10):
            x = func(y)
            print(x)
        x = 10
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_y, assign_x1, assign_x2, assign_x3 = mod.nodes_of_class(astroid.Assign)

        self.checker.visit_module(mod)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='redundant-assignment',
                    node=assign_y,
                ),
                pylint.testutils.Message(
                    msg_id='redundant-assignment',
                    node=assign_x1,
                ),
        ):
            self.checker.visit_assign(assign_y)
            self.checker.visit_assign(assign_x1)
            self.checker.visit_assign(assign_x2)
            self.checker.visit_assign(assign_x3)

    def test_message_scope(self):
        src = """
        x = 25
        def func():
            def func2():
                print(x - 1)
            func2()
        x = 10
        func()
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_x, *_ = mod.nodes_of_class(astroid.Assign)

        self.checker.visit_module(mod)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='redundant-assignment',
                    node=assign_x,
                )
        ):
            self.checker.visit_assign(assign_x)

    def test_no_message_loop_complex(self):
        src = """
        x = 10
        for y in range(1, 10):
            x = func(y)
            print(x)
        x = x - 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_x1, assign_x2, assign_x3 = mod.nodes_of_class(astroid.Assign)

        self.checker.visit_module(mod)
        with self.assertNoMessages():
            self.checker.visit_assign(assign_x1)
            self.checker.visit_assign(assign_x2)
            self.checker.visit_assign(assign_x3)

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
        for y in range(1, 10):
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

    def test_no_message_function_def(self):
        src = """
        x = 10
        if False:
            x = 20
        else:
            def func():
                x = 1
        print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        assign_x, *_ = mod.nodes_of_class(astroid.Assign)

        self.checker.visit_module(mod)
        with self.assertNoMessages():
            self.checker.visit_assign(assign_x)

    def test_augassign_simple_no_message(self):
        src = """
        y_pos = 5
        y_pos += 10
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())

        self.checker.visit_module(mod)
        with self.assertNoMessages():
            for node in mod.nodes_of_class(astroid.Assign):
                self.checker.visit_assign(node)
            for node in mod.nodes_of_class(astroid.AugAssign):
                self.checker.visit_augassign(node)

    def test_augassign_multiple_no_message(self):
        src = """
        y_pos = 5
        y_pos += 10
        y_pos += 10
        y_pos += 10
        y_pos += 10
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())

        self.checker.visit_module(mod)
        with self.assertNoMessages():
            for node in mod.nodes_of_class(astroid.Assign):
                self.checker.visit_assign(node)
            for node in mod.nodes_of_class(astroid.AugAssign):
                self.checker.visit_augassign(node)

    def test_augassign_redundant(self):
        src = """
        y_pos = 5
        y_pos += 10
        y_pos = 10
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        augassign_node, *_ = mod.nodes_of_class(astroid.AugAssign)

        self.checker.visit_module(mod)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='redundant-assignment',
                    node=augassign_node,
                )
        ):
            self.checker.visit_augassign(augassign_node)
