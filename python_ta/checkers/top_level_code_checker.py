"""Checker for top-level code"""

import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.base import UpperCaseStyle
from pylint.checkers.base.name_checker.checker import DEFAULT_PATTERNS
from pylint.checkers.utils import only_required_for_messages
from pylint.lint import PyLinter


class TopLevelCodeChecker(BaseChecker):
    """A checker class that reports forbidden top-level code"""

    name = "top_level_code"
    msgs = {
        "E9992": (
            "Forbidden top-level code found on line %s",
            "forbidden-top-level-code",
            "Used when you write top-level code that is not allowed. "
            "The allowed top-level code includes imports, definitions, and assignments.",
        )
    }

    @only_required_for_messages("forbidden-top-level-code")
    def visit_module(self, node: nodes.Module) -> None:
        """Visit module"""
        for statement in node.body:
            if not (
                _is_import(statement)
                or _is_definition(statement)
                or _is_allowed_assignment(statement)
                or _is_main_block(statement)
            ):
                self.add_message("forbidden-top-level-code", node=statement, args=statement.lineno)


def _is_import(statement: nodes.NodeNG) -> bool:
    """
    Return whether or not <statement> is an Import or an ImportFrom.
    """
    return isinstance(statement, (nodes.Import, nodes.ImportFrom))


def _is_definition(statement: nodes.NodeNG) -> bool:
    """
    Return whether or not <statement> is a function definition or a class definition.
    """
    return isinstance(statement, (nodes.FunctionDef, nodes.ClassDef))


def _is_allowed_assignment(statement: nodes.NodeNG) -> bool:
    """
    Return whether or not <statement> is a constant assignment or type alias assignment.
    """
    if not isinstance(statement, nodes.Assign) and not isinstance(statement, nodes.AnnAssign):
        return False

    names = []
    if isinstance(statement, nodes.Assign):
        for target in statement.targets:
            names.extend(node.name for node in target.nodes_of_class(nodes.AssignName, nodes.Name))
    else:
        names.extend(
            node.name for node in statement.target.nodes_of_class(nodes.AssignName, nodes.Name)
        )

    return names and all(
        re.match(UpperCaseStyle.CONST_NAME_RGX, name)
        or re.match(DEFAULT_PATTERNS["typealias"], name)
        for name in names
    )


def _is_main_block(statement: nodes.NodeNG) -> bool:
    """
    Return whether or not <statement> is the main block.
    """
    return (
        isinstance(statement, nodes.If)
        and isinstance(statement.test, nodes.Compare)
        and isinstance(statement.test.left, nodes.Name)
        and isinstance(statement.test.left, nodes.Name)
        and statement.test.left.name == "__name__"
        and len(statement.test.ops) == 1
        and statement.test.ops[0][0] == "=="
        and isinstance(statement.test.ops[0][1], nodes.Const)
        and statement.test.ops[0][1].value == "__main__"
    )


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(TopLevelCodeChecker(linter))
