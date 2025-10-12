"""Checker to check for unncessary f-strings that only consist of unmodified variables"""

from __future__ import annotations

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class FormattedStringChecker(BaseChecker):
    """A checker class that reports unnecessary uses of f-strings when they can be replaced
    with the variable directly"""

    name = "unnecessary-f-string"
    msgs = {
        "E9920": (
            'Unnecessary use of f-strings in the expression "f{%s}". Use "str(%s)" instead.',
            "unnecessary-f-string",
            "Used when the use of an f-string is unnecessary and can be replaced with the variable directly",
        )
    }

    def visit_joinedstr(self, node: nodes.JoinedStr) -> None:
        "Visits joined string"
        if len(node.values) == 1 and isinstance(node.values[0], nodes.FormattedValue):
            if node.values[0].conversion == -1 and node.values[0].format_spec is None:
                expression = node.values[0].value.as_string()
                self.add_message(
                    "unnecessary-f-string",
                    node=node,
                    args=(expression, expression),
                    line=node.lineno,
                    col_offset=node.col_offset,
                )


def register(linter: PyLinter) -> None:
    linter.register_checker(FormattedStringChecker(linter))
