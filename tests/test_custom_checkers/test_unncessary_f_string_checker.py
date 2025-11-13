import os

import pylint.testutils
from astroid import nodes, parse

from python_ta.checkers.unnecessary_f_string_checker import FormattedStringChecker


class TestFormattedStringChecker(pylint.testutils.CheckerTestCase):
    CHECKER_CLASS = FormattedStringChecker

    def test_unnecessary_f_string(self) -> None:
        """Tests for when using an f-string is unnecessary"""
        src = """
        var = 5
        x = f"{var}"
        """

        mod = parse(src)
        fstring_node, *_ = mod.nodes_of_class(nodes.JoinedStr)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unnecessary-f-string",
                node=fstring_node,
                line=2,
                args=("var", "var"),
            ),
            ignore_position=True,
        ):
            self.checker.visit_joinedstr(fstring_node)

    def test_f_string_with_formatting(self) -> None:
        """Tests for when f-string expression is being formatted"""
        src = """
        var = 5
        x = f"{var=  }"
        """

        mod = parse(src)
        fstring_node, *_ = mod.nodes_of_class(nodes.JoinedStr)
        with self.assertNoMessages():
            self.checker.visit_joinedstr(fstring_node)

    def test_f_string_with_expression(self) -> None:
        """Tests for when inner f-string expression modifies variable"""
        src = """
        var = 5
        x = f"{var + 1}"
        """

        mod = parse(src)
        fstring_node, *_ = mod.nodes_of_class(nodes.JoinedStr)
        with self.assertAddsMessages(
            pylint.testutils.MessageTest(
                msg_id="unnecessary-f-string",
                node=fstring_node,
                line=2,
                args=("var + 1", "var + 1"),
            ),
            ignore_position=True,
        ):
            self.checker.visit_joinedstr(fstring_node)

    def test_f_string_joined(self) -> None:
        """Tests for when inner f-string expression modifies variable"""
        src = """
        var = "world"
        x = f"hello, {var}"
        """

        mod = parse(src)
        fstring_node, *_ = mod.nodes_of_class(nodes.JoinedStr)
        with self.assertNoMessages():
            self.checker.visit_joinedstr(fstring_node)

    def test_f_string_multiple(self) -> None:
        """Tests for when f-string contains multiple variables"""
        src = """
        var1 = "hello"
        var2 = "world"
        x = f"{var1} {var2}"
        """

        mod = parse(src)
        fstring_node, *_ = mod.nodes_of_class(nodes.JoinedStr)
        with self.assertNoMessages():
            self.checker.visit_joinedstr(fstring_node)
