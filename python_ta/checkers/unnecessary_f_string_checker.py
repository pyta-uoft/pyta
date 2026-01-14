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
            "Unnecessary use of an f-string in the expression %s. Use %s instead.",
            "unnecessary-f-string",
            "Used when the use of an f-string is unnecessary and can be replaced with the variable directly",
        )
    }

    @only_required_for_messages("unnecessary-f-string")
    def visit_joinedstr(self, node: nodes.JoinedStr) -> None:
        if (
            len(node.values) == 1
            and isinstance(node.values[0], nodes.FormattedValue)
            and node.values[0].conversion == -1
            and node.values[0].format_spec is None
        ):
            expression = node.values[0].value.as_string()
            max_backtick_count = self.backtick_count(expression)
            f_string_message = (
                f'{"`" * max_backtick_count}f"{{{expression}}}"{"`" * max_backtick_count}'
            )
            str_message = f"{"`" * max_backtick_count}str({expression}){"`" * max_backtick_count}"
            self.add_message(
                "unnecessary-f-string",
                node=node,
                args=(f_string_message, str_message),
                line=node.lineno,
                col_offset=node.col_offset,
            )

    def backtick_count(self, input_str: str) -> int:
        """
        Return the length of the longest substring of consecutive backticks in input_str + 1
        """
        max_length = 0
        last_backtick = False
        for char in input_str:
            if char == "`":
                if last_backtick:
                    curr_length += 1
                else:
                    curr_length = 1
                    last_backtick = True
            elif last_backtick:
                if max_length < curr_length:
                    max_length = curr_length
                last_backtick = False
        return max_length + 1


def register(linter: PyLinter) -> None:
    linter.register_checker(FormattedStringChecker(linter))
