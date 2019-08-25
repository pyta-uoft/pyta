import pylint.testutils
import astroid
from python_ta.checkers.possible_infinite_loop_checker import \
    PossibleInfiniteLoopChecker
from python_ta.cfg import CFGVisitor


class TestPossiblyUndefinedChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PossibleInfiniteLoopChecker

    def test_no_messages_simple(self):
        src = """
        def test(x):
            x = 10
            if True:
                return x
            return x
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        name_node_a, name_node_b = mod.nodes_of_class(astroid.Name)

        with self.assertNoMessages():
            self.checker.visit_module(mod)
            self.checker.visit_functiondef(func_node)
            self.checker.visit_name(name_node_a)
            self.checker.visit_name(name_node_b)

    def test_no_messages_with_args(self):
        src = """
        def test(x):
            if True:
                x = 10
            print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, name_node_x = mod.nodes_of_class(astroid.Name)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_name(name_node_x)

    def test_no_messages_if_else(self):
        src = """
        def test(x):
            if True:
                y = 10
            else:
                y = 20
            print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, name_node_y = mod.nodes_of_class(astroid.Name)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_name(name_node_y)

    def test_no_messages_if_else_with_ann_assign(self):
        src = """
        def test(x):
            if True:
                y: int = 10
            else:
                y = 20
            print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, _, name_node_y = mod.nodes_of_class(astroid.Name)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_name(name_node_y)

    def test_no_messages_complex(self):
        src = """
        def test(x):
            if True:
                y = 10
            else:
                for j in range(10):
                    if j > 10:
                        y = 10
                        break
                else:
                    y = 10
            return y
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, _, name_node_y = mod.nodes_of_class(astroid.Name)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_name(name_node_y)

    def test_no_messages_with_nonlocal(self):
        src = """
        def test(x):
            x = 10
            nonlocal y
            if True:
                y = 10
            print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        __, name_node_y = mod.nodes_of_class(astroid.Name)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_name(name_node_y)

    def test_no_messages_with_global(self):
        src = """
        def test(x):
            x = 10
            if True:
                y = 10
            else:
                global y
            print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, name_node_y = mod.nodes_of_class(astroid.Name)

        with self.assertNoMessages():
            self.checker.visit_functiondef(func_node)
            self.checker.visit_name(name_node_y)

    def test_no_messages_with_class_def(self):
        """This example is a false negative due to how class definitions are
        represented in the control flow graph."""
        src = """
        class A:
            y = 10

        if True:
            x = 10
        else:
            y = 20
        print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        _, name_node_y = mod.nodes_of_class(astroid.Name)

        self.checker.visit_module(mod)
        with self.assertNoMessages():
            self.checker.visit_name(name_node_y)

    def test_message_simple(self):
        src = """
        x = 10
        if True:
            y = 10
        else:
            x = 10
        print(x and y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        _, name_node_x, name_node_y = mod.nodes_of_class(astroid.Name)

        self.checker.visit_module(mod)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possibly-undefined',
                    node=name_node_y,
                ),
        ):
            self.checker.visit_name(name_node_y)

        with self.assertNoMessages():
            self.checker.visit_name(name_node_x)

    def test_message_with_del(self):
        src = """
        def test(x):
            y = 10
            if True:
                x = 20
            else:
                del y
            print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, name_node_y = mod.nodes_of_class(astroid.Name)

        self.checker.visit_functiondef(func_node)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possibly-undefined',
                    node=name_node_y,
                ),
        ):
            self.checker.visit_name(name_node_y)

    def test_message_complex(self):
        src = """
        def test(x):
            if True:
                y = 10
            else:
                for j in range(10):
                    if j > 10:
                        break
                else:
                    y = 10
            return y
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, _, name_node_y = mod.nodes_of_class(astroid.Name)

        self.checker.visit_functiondef(func_node)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possibly-undefined',
                    node=name_node_y,
                ),
        ):
            self.checker.visit_name(name_node_y)

    def test_message_with_args(self):
        src = """
        def test(x):
            if True:
                del x
            print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, name_node_x = mod.nodes_of_class(astroid.Name)

        self.checker.visit_functiondef(func_node)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possibly-undefined',
                    node=name_node_x,
                ),
        ):
            self.checker.visit_name(name_node_x)

    def test_multiple_messages_simple(self):
        src = """
        if True:
            y: int = 10
        else:
            x = 10
        print(x and y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        _, _, name_node_x, name_node_y = mod.nodes_of_class(astroid.Name)

        self.checker.visit_module(mod)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possibly-undefined',
                    node=name_node_y,
                ),
                pylint.testutils.Message(
                    msg_id='possibly-undefined',
                    node=name_node_x,
                )
        ):
            self.checker.visit_name(name_node_y)
            self.checker.visit_name(name_node_x)

    def test_message_with_nested_func(self):
        """This example targets the part of the checker implementation that traverses
        the ast using Node.nodes_of_class or anything equivalent."""
        src = """
        def func(x):
            if True:
                y = 10
            else:
                def func2():
                    y = 20
            print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        func_node = mod.body[0]
        _, name_node_y = mod.nodes_of_class(astroid.Name)

        self.checker.visit_functiondef(func_node)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possibly-undefined',
                    node=name_node_y,
                )
        ):
            self.checker.visit_name(name_node_y)
