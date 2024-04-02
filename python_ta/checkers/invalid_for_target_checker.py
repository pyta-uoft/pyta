"""Checker for target of for loop or comprehension in subscript form.
"""

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class InvalidForTargetChecker(BaseChecker):
    """A checker class that reports on the invalid use of targets in for loops or comprehensions"""

    name = "invalid_for_target"
    msgs = {
        "E9984": (
            'For loop or comprehension variable "%s" should not be a part of a larger object.',
            "invalid-for-target",
            "Used when you have an index variable in a for loop or comprehension"
            "that is in subscript or object attribute form",
        )
    }

    INVALID_TARGETS = (nodes.Subscript, nodes.AssignAttr)

    @only_required_for_messages("invalid-for-target")
    def visit_for(self, node: nodes.For) -> None:
        """Visits the for node"""
        invalid_for_targets = node.target.nodes_of_class(self.INVALID_TARGETS)
        for target in invalid_for_targets:
            self.add_message("invalid-for-target", node=target, args=target.as_string())

    @only_required_for_messages("invalid-for-target")
    def visit_comprehension(self, node: nodes.Comprehension) -> None:
        """Visits the comprehension node"""
        invalid_for_targets = node.target.nodes_of_class(self.INVALID_TARGETS)
        for target in invalid_for_targets:
            self.add_message("invalid-for-target", node=target, args=target.as_string())


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(InvalidForTargetChecker(linter))
