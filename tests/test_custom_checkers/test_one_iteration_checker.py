import astroid
import pylint.testutils
import pytest
from astroid import nodes

from python_ta.cfg.visitor import CFGVisitor
from python_ta.checkers.one_iteration_checker import OneIterationChecker
from python_ta.transforms.z3_visitor import Z3Visitor


class TestOneIterationChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = OneIterationChecker

    @pytest.mark.parametrize(
        "src,node_type",
        [
            (
                """
                def func(x: int) -> int:
                    while x > 5:
                        x -= 1
                        return x
                    return 0
                """,
                nodes.While,
            ),
            (
                """
                x = 1
                while x < 5:
                    x += 1
                    break
                print(x)
                """,
                nodes.While,
            ),
            (
                """
                def func(x: list[int]) -> int:
                    for i in x:
                        return i
                """,
                nodes.For,
            ),
            (
                """
                for i in range(10):
                    break
                print(i)
                """,
                nodes.For,
            ),
            (
                """
                def func(x: int) -> int:
                    while x > 5:
                        if x % 2 == 0:
                            return True
                        else:
                            return False
                        x -= 1
                """,
                nodes.While,
            ),
            (
                """
                x = 10
                while x > 5:
                    if x % 2 == 0:
                        print("even")
                        break
                    else:
                        print("odd")
                        break
                    x -= 1
                """,
                nodes.While,
            ),
            (
                """
                def func(x: int) -> int:
                    for i in range(10):
                        if i % 2 == 0:
                            return True
                        else:
                            return False
                """,
                nodes.For,
            ),
            (
                """
                for i in range(10):
                    if i % 2 == 0:
                        print("even")
                        break
                    else:
                        print("odd")
                        break
                """,
                nodes.For,
            ),
            (
                """
                def func(x: int) -> bool:
                    while x > 5:
                        if x % 2 == 0:
                            if x > 8:
                                return True
                            else:
                                return False
                        else:
                            return False
                """,
                nodes.While,
            ),
            (
                """
                for i in range(10):
                    for j in range(5):
                        break
                    break
                """,
                nodes.For,
            ),
            (
                """
                for i in range(10):
                    while i < 5:
                        if i == 3:
                            break
                    break
                """,
                nodes.For,
            ),
        ],
        ids=[
            "while_with_return",
            "while_with_break",
            "for_loop_with_return",
            "for_loop_with_break",
            "while_with_return_all_branches",
            "while_with_break_all_branches",
            "for_loop_with_return_all_branches",
            "for_loop_with_break_all_branches",
            "nested_if_else_with_return",
            "nested_for_loops",
            "for_with_nested_while_and_break",
        ],
    )
    def test_one_iteration_message(self, src, node_type):
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        loop_node = next(mod.nodes_of_class(node_type))
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="one-iteration",
                node=loop_node,
            ),
            ignore_position=True,
        ):
            if isinstance(loop_node, nodes.While):
                self.checker.visit_while(loop_node)
            else:
                self.checker.visit_for(loop_node)

    def test_while_with_return_some_branches(self):
        src = """
        def func(x: int) -> int:
            while x > 5:
                if x % 2 == 0:
                    return True
                else:
                    x -= 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_while_with_break_some_branches(self):
        src = """
        x = 10
        while x > 5:
            if x % 2 == 0:
                print("even")
                break
            else:
                x -= 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_while_loop_without_termination(self):
        src = """
        while True:
            print("loading...")
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        for_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_for_loop_with_return_some_branches(self):
        src = """
        def func(x: int) -> int:
            for i in range(10):
                if i % 2 == 0:
                    return True
                else:
                    x -= 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        for_node = next(mod.nodes_of_class(nodes.For))

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_for_loop_with_break_some_branches(self):
        src = """
        for i in range(10):
            if i % 2 == 0:
                print("even")
                break
            else:
                i -= 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        for_node = next(mod.nodes_of_class(nodes.For))

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_for_loop_without_termination(self):
        src = """
        for i in range(10):
            i += 1
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        for_node = next(mod.nodes_of_class(nodes.For))

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_while_with_continue_only(self):
        src = """
        x = 10
        while x > 5:
            if x % 2 == 0:
                x -= 1
                continue
            else:
                break
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_nested_while_loops(self):
        src = """
        x = 10
        y = 5
        while x > 5:
            while y > 3:
                if x > 3:
                    break
            break
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        while_node1, while_node2 = mod.nodes_of_class(nodes.While)

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="one-iteration",
                node=while_node1,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(while_node1)

        with self.assertNoMessages():
            self.checker.visit_while(while_node2)

    def test_nested_for_with_continue_and_return(self):
        src = """
        for i in range(10):
            for j in range(5):
                if j == 2:
                    continue
                return i + j
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        for_node = next(mod.nodes_of_class(nodes.For))

        with self.assertNoMessages():
            self.checker.visit_for(for_node)

    def test_while_with_try_finally(self):
        src = """
        x = 10
        while x > 5:
            try:
                return x
            finally:
                print('cleanup')
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_while_with_try_except(self):
        src = """
        x = 10
        while x > 5:
            try:
                return x
            except Exception:
                print('error')
        """
        mod = astroid.parse(src)
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)


class TestOneIterationCheckerZ3Option(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = OneIterationChecker
    CONFIG = {"z3": True}

    def test_z3_one_iteration_break_by_precondition(self):
        src = """
        def func(x: int) -> int:
            '''
            Preconditions:
                - x > 5
            '''
            while x > 0:
                if x > 3:
                    break
                print(x)
            return x
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="one-iteration",
                node=while_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(while_node)

    def test_z3_one_iteration_break_by_precondition_no_loop_body(self):
        src = """
        def func(x: int) -> int:
            '''
            Preconditions:
                - x > 5
            '''
            while x > 0:
                if x > 3:
                    break
            return x
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="one-iteration",
                node=while_node,
            ),
            ignore_position=True,
        ):
            self.checker.visit_while(while_node)

    def test_z3_multiple_iterations(self):
        src = """
        def func(x: int, y: bool) -> int:
            '''
            Preconditions:
                - x > 5
            '''
            while x > 0:
                if x > 3 and y:
                    break
                print(x)
            return x
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_z3_one_iteration_for_loop(self):
        src = """
         def func(x: float) -> int:
            '''
            Preconditions:
                - x in [1.0, 2.0, 3.0]
            '''
            for i in range(0, 3):
                if x == 3.0:
                    break
            return x
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        for_node = next(mod.nodes_of_class(nodes.For))

        with self.assertNoMessages():
            self.checker.visit_while(for_node)

    def test_z3_one_iteration_unfeasible_loop_body(self):
        src = """
        def func(x: int):
            '''
            Preconditions:
                - x > 10
            '''
            while x < 0:
                print("unfeasible")
                break
            print("end")
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)

    def test_z3_one_iteration_unfeasible_loop_statement(self):
        src = """
        def func(x: int):
            '''
            Preconditions:
                - x > 10
            '''
            if x < 0:
                while x > 0:
                    print("unfeasible")
                    break
            print("end")
        """
        z3v = Z3Visitor()
        mod = z3v.visitor.visit(astroid.parse(src))
        mod.accept(CFGVisitor())
        while_node = next(mod.nodes_of_class(nodes.While))

        with self.assertNoMessages():
            self.checker.visit_while(while_node)
