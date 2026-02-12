"""
Check for invalid syntax within function preconditons.
"""

import ast

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter

from python_ta.contracts import parse_assertions


class InvalidPreconditionSyntaxChecker(BaseChecker):
    """A checker that reports invalid Python syntax within function preconditions"""

    name = "invalid-precondition-checker"
    msgs = {
        "E9980": (
            "Invalid syntax in precondition: %s",
            "invalid-precondition-syntax",
            "Reported when a precondition contains invalid Python syntax.",
        )
    }

    @only_required_for_messages("invalid-precondition-syntax")
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit function definition and check preconditions in docstring."""

        if not node.doc_node:
            return

        preconditions = parse_assertions(node, parse_token="Precondition")
        for condition in preconditions:
            try:
                ast.parse(condition, mode="eval")
            except SyntaxError:
                self.add_message("invalid-precondition-syntax", node=node, args=(condition,))


def register(linter: PyLinter) -> None:
    linter.register_checker(InvalidPreconditionSyntaxChecker(linter))
