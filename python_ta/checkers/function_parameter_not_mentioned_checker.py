"""checker that every function parameter is mentioned by name in the docstring text.
"""

from __future__ import annotations

from typing import Optional

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class FunctionParameterNotMentionedChecker(BaseChecker):
    """
    A class checker to check if every function parameter is mentioned by name within it's the docstring.
    By default, this checker will be disabled.
    """

    name = "function_parameters_not_mentioned"
    msgs = {
        "C9960": (
            "The parameter '%s' is not mentioned in the docstring",
            "function-parameters-not-mentioned",
            "Used when a function parameter is not mentioned in the docstring",
        )
    }

    def __init__(self, linter: Optional[PyLinter] = None) -> None:
        super().__init__(linter=linter)

    @only_required_for_messages("function-parameters-not-mentioned")
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit a function definition"""
        docstring = node.doc_node.value if node.doc_node and node.doc_node.value else ""
        self._check_parameters(self._strip_docstring_of_doctest(docstring), node.argnames(), node)

    # Helper Function
    def _check_parameters(self, docstring: str, parameters: list[str], node: nodes.NodeNG) -> None:
        """Check if every parameter is mentioned in the docstring"""
        words = {word.strip(".,:") for line in docstring.split("\n") for word in line.split()}
        for parameter in parameters:
            if not (words and parameter in words):
                self.add_message(
                    "function-parameters-not-mentioned", node=node, args=parameter, line=node.lineno
                )

    def _strip_docstring_of_doctest(self, docstring: str) -> str:
        """Return the docstring without the doctest"""
        start_index = docstring.find(">>>")
        contains_doctest = start_index != -1
        if contains_doctest:
            return docstring[:start_index]
        return docstring


def register(linter: PyLinter) -> None:
    """Required method to auto register this checker on the linter"""
    linter.register_checker(FunctionParameterNotMentionedChecker(linter))
