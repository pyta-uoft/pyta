import pylint.testutils
from astroid import extract_node, nodes, parse

from python_ta.checkers.simplifiable_if_checker import SimplifiableIfChecker


class TestSimplifiableIfChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = SimplifiableIfChecker

    def test_simplifiable_if(self) -> None:
        """Tests for when an if statement can be simplified"""

        src = """
        x = 10
        if x > 5:
            if x < 10:
                x += 1
        """

        mod = parse(src)
        if_node, *_ = mod.nodes_of_class(nodes.If)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="simplifiable-if",
                node=if_node.body[0].test,
                line=3,
            ),
            ignore_position=True,
        ):
            self.checker.visit_if(if_node)

    def test_simplifiable_elif(self) -> None:
        """Tests for when an elif statement can be simplified"""

        src = """
        x = 10
        if x > 5:
            x += 5
        elif x < -5: #@
            if x > -10:
                x -= 1
        """

        if_node = extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="simplifiable-if", node=if_node.body[0].test, line=5
            ),
            ignore_position=True,
        ):
            self.checker.visit_if(if_node)

    def test_doubly_nested_elif(self) -> None:
        src = """
        x = 10
        if x > 1:
            x = 5
        elif x < -2: #@
            if x > -1:
                if x == 0:
                    x = 3
        """
        elif_node = extract_node(src)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="simplifiable-if",
                node=elif_node.body[0].test,
                line=5,
            ),
            pylint.testutils.MessageTest(
                msg_id="simplifiable-if",
                node=elif_node.body[0].body[0].test,
                line=6,
            ),
            ignore_position=True,
        ):
            self.checker.visit_if(elif_node)
            self.checker.visit_if(elif_node.body[0])

    def test_doubly_nested_if(self) -> None:
        src = """
        x = 10
        if x > 1:
            if x > 2:
                if x > 3:
                    x += 1
        """
        mod = parse(src)
        if_node, *_ = mod.nodes_of_class(nodes.If)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="simplifiable-if",
                node=if_node.body[0].test,
                line=3,
            ),
            pylint.testutils.MessageTest(
                msg_id="simplifiable-if",
                node=if_node.body[0].body[0].test,
                line=4,
            ),
            ignore_position=True,
        ):
            self.checker.visit_if(if_node)
            self.checker.visit_if(if_node.body[0])

    def test_no_simplification(self) -> None:
        """Tests for when no simplification can be made"""

        src = """
        x = 10
        if x > 5:
            x += 5
        elif x < -5:
            x -= 10
        else:
            x = 50
        """

        mod = parse(src)
        if_node, *_ = mod.nodes_of_class(nodes.If)
        with self.assertNoMessages():
            self.checker.visit_if(if_node)

    def test_no_simplification_multiple_branches(self) -> None:
        src = """
        x = 10
        if x > 1: #@
            if x < 1:
                x = 5
        elif x < -2: #@
            if x > -1:
                if x == 0:
                    x = 3
        else:
            x = 5
        """
        if_node, elif_node = extract_node(src)
        with self.assertNoMessages():
            self.checker.visit_if(if_node)
            self.checker.visit_if(elif_node)
