"""
Check for invalid syntax within function preconditons.
"""

import ast
import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter

from ..contracts import FUNCTION_RETURN_VALUE, parse_assertions


class ContractChecker(BaseChecker):
    """A checker class that validates Python contract syntax."""

    name = "contract-checker"
    msgs = {
        "E9980": (
            "Invalid syntax in precondition: %s",
            "invalid-precondition-syntax",
            "Reported when a precondition contains invalid Python expression syntax.",
        ),
        "E9981": (
            "Invalid syntax in postcondition: %s",
            "invalid-postcondition-syntax",
            "Reported when a postcondition contains invalid Python expression syntax.",
        ),
    }

    @only_required_for_messages("invalid-precondition-syntax", "invalid-postcondition-syntax")
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit function definition and check preconditions and postconditions in docstring."""

        if not node.doc_node:
            return

        preconditions = parse_assertions(node, parse_token="Precondition")
        for precondition in preconditions:
            cleaned_precondition = re.sub(r"\s+", " ", precondition)
            try:
                ast.parse(cleaned_precondition, mode="eval")
            except SyntaxError:
                self.add_message(
                    "invalid-precondition-syntax", node=node, args=(cleaned_precondition,)
                )

        postconditions = parse_assertions(node, parse_token="Postcondition")
        for postcondition in postconditions:
            cleaned_postcondition = re.sub(r"\s+", " ", postcondition)
            parseable_condition = cleaned_postcondition.replace(
                FUNCTION_RETURN_VALUE, "_return_value"
            )
            try:
                ast.parse(parseable_condition, mode="eval")
            except SyntaxError:
                self.add_message(
                    "invalid-postcondition-syntax", node=node, args=(cleaned_postcondition,)
                )


def register(linter: PyLinter) -> None:
    linter.register_checker(ContractChecker(linter))
