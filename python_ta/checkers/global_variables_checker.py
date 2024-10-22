"""Checker for global variables
"""

from __future__ import annotations

import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.base import UpperCaseStyle
from pylint.checkers.base.name_checker.checker import DEFAULT_PATTERNS
from pylint.checkers.utils import is_builtin
from pylint.lint import PyLinter

from python_ta.utils import _is_in_main


class GlobalVariablesChecker(BaseChecker):
    """A checker class that reports the forbidden global variables in the file"""

    name = "global_variables"
    msgs = {
        "E9997": (
            "Global variables must be constants or type aliases in CSC108/CSC148: " "%s",
            "forbidden-global-variables",
            "",
        )
    }

    def __init__(self, linter=None) -> None:
        super().__init__(linter)
        self.import_names = []

    def visit_global(self, node: nodes.Global) -> None:
        args = "the keyword 'global' is used on line {}".format(node.lineno)
        self.add_message("forbidden-global-variables", node=node, args=args)

    def visit_assignname(self, node: nodes.AssignName) -> None:
        """Allow global constant variables (uppercase) and type aliases (type alias pattern), but issue messages for
        all other globals.
        """
        self._inspect_vars(node)

    def visit_name(self, node: nodes.Name) -> None:
        """Allow global constant variables (uppercase) and type aliases (type alias pattern), but issue messages for
        all other globals.
        """
        self._inspect_vars(node)

    def visit_import(self, node: nodes.Import) -> None:
        """Save the names of imports, to prevent mistaking for global vars."""
        self._store_name_or_alias(node)

    def visit_importfrom(self, node: nodes.ImportFrom) -> None:
        """Save the names of imports, to prevent mistaking for global vars."""
        self._store_name_or_alias(node)

    def _store_name_or_alias(self, node: nodes.NodeNG) -> None:
        for name_tuple in node.names:
            if name_tuple[1] is not None:
                self.import_names.append(name_tuple[1])  # aliased names
            else:
                self.import_names.append(name_tuple[0])  # no alias

    def _inspect_vars(self, node: nodes.NodeNG) -> None:
        """Allows constant, global variables (i.e. uppercase) and type aliases (i.e. type alias pattern), but issue
        messages for all other global variables.
        """
        if hasattr(node, "name") and node.name in self.import_names:
            return
        if isinstance(node.frame(), nodes.Module) and not _is_in_main(node):
            node_list = _get_child_disallowed_global_var_nodes(node)
            for node in node_list:
                if isinstance(node, nodes.AssignName):
                    args = "a global variable '{}' is assigned to on line {}".format(
                        node.name, node.lineno
                    )
                else:
                    args = "a global variable '{}' is used on line {}".format(
                        node.name, node.lineno
                    )
                self.add_message("forbidden-global-variables", node=node, args=args)


def _get_child_disallowed_global_var_nodes(node: nodes.NodeNG) -> list[nodes.NodeNG]:
    """Return a list of all top-level Name or AssignName nodes for a given
    global, non-constant and non-type alias variable.
    """
    node_list = []
    if (
        (
            isinstance(node, (nodes.AssignName, nodes.Name))
            and not isinstance(node.parent, nodes.Call)
        )
        and not (
            re.match(UpperCaseStyle.CONST_NAME_RGX, node.name)
            or re.match(DEFAULT_PATTERNS["typealias"], node.name)
        )
        and not is_builtin(node.name)
        and node.scope() is node.root()
    ):
        return [node]

    for child_node in node.get_children():
        node_list += _get_child_disallowed_global_var_nodes(child_node)
    return node_list


def register(linter: PyLinter) -> None:
    """Required method to auto-register this checker to the linter"""
    linter.register_checker(GlobalVariablesChecker(linter))
