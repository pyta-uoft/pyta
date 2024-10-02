"""checker that every function parameter is mentioned by name in the docstring text.
"""

from __future__ import annotations

import doctest
import string

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class FunctionParameterNotMentionedChecker(BaseChecker):
    """
    A class to check if every function parameter is mentioned by name within the function's the docstring.
    By default, this checker is disabled.
    """

    name = "unmentioned-parameter"
    msgs = {
        "C9960": (
            "The parameter '%s' is not mentioned in the docstring",
            "unmentioned-parameter",
            "Used when a function parameter is not mentioned in the docstring",
        )
    }

    @only_required_for_messages("unmentioned-parameter")
    def visit_functiondef(self, node: nodes.FunctionDef) -> None:
        """Visit a function definition"""
        docstring = node.doc_node.value if node.doc_node and node.doc_node.value else ""
        for parameter in node.args.args:
            self._check_parameters(
                self._strip_docstring_of_doctest(docstring), parameter.name, parameter
            )

    # Helper Function
    def _check_parameters(self, docstring: str, parameter: str, node: nodes.NodeNG) -> None:
        """Check if every parameter is mentioned in the docstring"""
        translator = str.maketrans("", "", string.punctuation)
        docstring = docstring.translate(translator)
        words = {word for line in docstring.split("\n") for word in line.split()}
        if parameter not in words:
            self.add_message("unmentioned-parameter", node=node, args=parameter, line=node.lineno)

    def _strip_docstring_of_doctest(self, docstring: str) -> str:
        """Return the docstring without the doctest"""
        parsed = doctest.DocTestParser().parse(docstring)
        return "".join(part for part in parsed if not isinstance(part, doctest.Example))


def register(linter: PyLinter) -> None:
    """Required method to auto register this checker on the linter"""
    linter.register_checker(FunctionParameterNotMentionedChecker(linter))
