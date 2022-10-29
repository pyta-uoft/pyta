"""Checker for target of for loop or comprehension in subscript form.
"""
from typing import List, Union

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.utils import only_required_for_messages


class InvalidForTargetChecker(BaseChecker):
    # name is the same as file name but without _checker part
    name = "invalid_for_target"
    # use dashes for connecting words in message symbol
    msgs = {
        "E9984": (
            'For loop or comprehension variable "%s" should not be a part of a larger object.',
            "invalid-for-target",
            "Used when you have an index variable in a for loop or comprehension"
            "that is in subscript or object attribute form",
        )
    }
    # this is important so that your checker is executed before others
    priority = -1

    INVALID_TARGETS = (nodes.Subscript, nodes.AssignAttr)

    @only_required_for_messages("invalid-for-target")
    def visit_for(self, node: nodes.For) -> None:
        invalid_for_targets = node.target.nodes_of_class(self.INVALID_TARGETS)
        for target in invalid_for_targets:
            self.add_message("invalid-for-target", node=target, args=target.as_string())

    @only_required_for_messages("invalid-for-target")
    def visit_comprehension(self, node: nodes.Comprehension) -> None:
        invalid_for_targets = node.target.nodes_of_class(self.INVALID_TARGETS)
        for target in invalid_for_targets:
            self.add_message("invalid-for-target", node=target, args=target.as_string())


def register(linter):
    linter.register_checker(InvalidForTargetChecker(linter))
