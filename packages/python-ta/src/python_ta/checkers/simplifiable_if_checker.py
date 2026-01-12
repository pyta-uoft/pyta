"""Checker that checks for nested if statements that can be simplified"""

from __future__ import annotations

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class SimplifiableIfChecker(BaseChecker):
    """A checker class that reports nested if statements that can be simplified"""

    name = "simplifiable-if"
    msgs = {
        "E9930": (
            "This nested `if` statement can be simplified. Combine the inner condition with the outer condition using the `and` operator and remove the nested `if` statement.",
            "simplifiable-if",
            "Used when an `if` or `elif` branch only contains a single nested `if` statement with a single branch.",
        )
    }

    @only_required_for_messages("simplifiable-if")
    def visit_if(self, node: nodes.If) -> None:
        if (
            len(node.body) == 1
            and not node.has_elif_block()
            and not node.orelse
            and isinstance(node.body[0], nodes.If)
            and not node.body[0].orelse
        ):
            inner_node = node.body[0]
            self.add_message(
                "simplifiable-if",
                node=inner_node.test,
                line=inner_node.lineno,
                col_offset=inner_node.col_offset,
            )


def register(linter: PyLinter) -> None:
    linter.register_checker(SimplifiableIfChecker(linter))
