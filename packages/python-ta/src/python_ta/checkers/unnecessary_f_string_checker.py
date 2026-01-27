"""Checker to check for unncessary f-strings that only consist of single expressions"""

from __future__ import annotations

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class FormattedStringChecker(BaseChecker):
    """A checker class that reports unnecessary uses of f-strings when they can be replaced
    with the expression directly"""

    name = "unnecessary-f-string"
    msgs = {
        "E9920": (
            'Unnecessary use of an f-string in the expression `f"{%s}"`. Use `str(%s)` instead.',
            "unnecessary-f-string",
            "Used when the use of an f-string is unnecessary and can be replaced with the variable directly",
        ),
        "E9921": (
            'Unnecessary use of an f-string in the expression `f"{%s}"`. Use `%s` instead.',
            "unnecessary-f-string-on-string",
            "Used when an f-string is unnecessary and wraps an expression that is already a string.",
        ),
    }

    @only_required_for_messages("unnecessary-f-string", "unnecessary-f-string-on-string")
    def visit_joinedstr(self, node: nodes.JoinedStr) -> None:
        if (
            len(node.values) == 1
            and isinstance(node.values[0], nodes.FormattedValue)
            and node.values[0].conversion == -1
            and node.values[0].format_spec is None
        ):
            expression = node.values[0].value.as_string()
            str_call_needed = False

            for inferred in node.values[0].value.infer():
                if isinstance(inferred, nodes.Const):
                    source = inferred.as_string()
                    if not (source.startswith(("'", '"'))):
                        str_call_needed = True
                        break
                else:
                    str_call_needed = True
                    break

            if str_call_needed:
                self.add_message(
                    "unnecessary-f-string",
                    node=node,
                    args=(expression, expression),
                    line=node.lineno,
                    col_offset=node.col_offset,
                )
            else:
                self.add_message(
                    "unnecessary-f-string-on-string",
                    node=node,
                    args=(expression, expression),
                    line=node.lineno,
                    col_offset=node.col_offset,
                )


def register(linter: PyLinter) -> None:
    linter.register_checker(FormattedStringChecker(linter))
