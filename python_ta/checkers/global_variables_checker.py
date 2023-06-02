"""checker for global variables
"""
import re

from astroid import nodes
from pylint.checkers import BaseChecker
from pylint.checkers.base import UpperCaseStyle
from pylint.checkers.base.name_checker.checker import DEFAULT_PATTERNS
from pylint.checkers.utils import is_builtin

from python_ta.utils import _is_in_main


class GlobalVariablesChecker(BaseChecker):
    name = "global_variables"
    msgs = {
        "E9997": (
            "Global variables must be constants or type aliases in CSC108/CSC148: " "%s",
            "forbidden-global-variables",
            "",
        )
    }

    # this is important so that your checker is executed before others
    priority = -1

    def __init__(self, linter=None):
        super().__init__(linter)
        self.import_names = []

    def visit_global(self, node):
        args = "the keyword 'global' is used on line {}".format(node.lineno)
        self.add_message("forbidden-global-variables", node=node, args=args)

    def visit_assignname(self, node):
        """Allow global constant variables (uppercase) and type aliases (type alias pattern), but issue messages for
        all other globals.
        """
        self._inspect_vars(node)

    def visit_name(self, node):
        """Allow global constant variables (uppercase) and type aliases (type alias pattern), but issue messages for
        all other globals.
        """
        self._inspect_vars(node)

    def visit_import(self, node):
        """Save the names of imports, to prevent mistaking for global vars."""
        self._store_name_or_alias(node)

    def visit_importfrom(self, node):
        """Save the names of imports, to prevent mistaking for global vars."""
        self._store_name_or_alias(node)

    def _store_name_or_alias(self, node):
        for name_tuple in node.names:
            if name_tuple[1] is not None:
                self.import_names.append(name_tuple[1])  # aliased names
            else:
                self.import_names.append(name_tuple[0])  # no alias

    def _inspect_vars(self, node):
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


def _get_child_disallowed_global_var_nodes(node):
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


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(GlobalVariablesChecker(linter))
