"""Checker for variable shadowing in a comprehension.
"""

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class ShadowingInComprehensionChecker(BaseChecker):
    """A checker class that reports a comprehension variable shadowing a variable in outer scope"""

    name = "shadowing_in_comprehension"
    msgs = {
        "E9988": (
            "Comprehension variable '%s' shadows a variable in an outer scope",
            "shadowing-in-comprehension",
            "Used when there is shadowing inside a comprehension",
        )
    }

    @only_required_for_messages("shadowing-in-comprehension")
    def visit_comprehension(self, node: nodes.Comprehension) -> None:
        """Visit the comprehension node"""
        if isinstance(node.target, nodes.Tuple):
            for target in node.target.elts:
                if target.name in node.parent.frame().locals and target.name != "_":
                    args = target.name
                    self.add_message("shadowing-in-comprehension", node=target, args=args)
        elif isinstance(node.target, nodes.AssignName):
            if node.target.name in node.parent.frame().locals and node.target.name != "_":
                args = node.target.name
                self.add_message("shadowing-in-comprehension", node=node.target, args=args)


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(ShadowingInComprehensionChecker(linter))
