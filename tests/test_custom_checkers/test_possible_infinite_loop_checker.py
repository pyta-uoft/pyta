import pylint.testutils
import astroid
from python_ta.checkers.possible_infinite_loop_checker import \
    PossibleInfiniteLoopChecker
from python_ta.cfg import CFGVisitor
from python_ta.transforms.type_inference_visitor import TypeInferer


class TestPossiblyUndefinedChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = PossibleInfiniteLoopChecker

    def test_no_message_simple(self):
        src = """
        x = 20
        while x > 10:
            x -= 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_no_message_func_call(self):
        src = """
        x = 'lol'
        while len(x) > 10:
            print(10)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_no_message_mutable_type_usage(self):
        src = """
        x = [1, 2, 3]
        while x:
            print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_no_message_mutable_type_assign(self):
        src = """
        x = [1, 2, 3]
        while x:
            x = False
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_no_message_multiple_vars(self):
        src = """
        x = [1, 2, 3]
        y = 123
        while x and y:
            x.pop()
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_no_message_global_var(self):
        src = """
        x = [1, 2, 3]
        def func():
            while x:
                mutate_x()
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_message_simple(self):
        src = """
        x = 'lol'
        while  x == '123':
            print(10)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possible-infinite-loop',
                    node=while_node,
                ),
        ):
            self.checker.visit_while(while_node)

    def test_message_immutable_type(self):
        src = """
        x = 'lol'
        while  x == '123':
            print(x)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possible-infinite-loop',
                    node=while_node,
                ),
        ):
            self.checker.visit_while(while_node)

    def test_message_mutable_type(self):
        src = """
        x = [1, 2, 3]
        while  x:
            print(10)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possible-infinite-loop',
                    node=while_node,
                ),
        ):
            self.checker.visit_while(while_node)

    def test_message_func_name_identical_to_var(self):
        src = """
        x = [1, 2, 3]
        while x:
            x()
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possible-infinite-loop',
                    node=while_node,
                ),
        ):
            self.checker.visit_while(while_node)

    def test_message_multiple_vars_immutable_type(self):
        src = """
        x = [1, 2, 3]
        y = 123
        while x and y:
            print(y)
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        type_inferer = TypeInferer()
        type_inferer.environment_transformer().visit(mod)
        type_inferer.type_inference_transformer().visit(mod)

        while_node, *_ = mod.nodes_of_class(astroid.While)
        with self.assertAddsMessages(
                pylint.testutils.Message(
                    msg_id='possible-infinite-loop',
                    node=while_node,
                ),
        ):
            self.checker.visit_while(while_node)
