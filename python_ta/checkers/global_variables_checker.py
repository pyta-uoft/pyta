"""checker for global variables
"""
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
import astroid
import re
from pylint.checkers.base import CONST_NAME_RGX


class GlobalVariablesChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'global_variables'
    msgs = {'E9997': ('Global variables should not be used in CSC108/CSC148 - '
                      '%s', 'forbidden-global-variables', '')}

    # this is important so that your checker is executed before others
    priority = -1

    def __init__(self, linter=None):
        super().__init__(linter)
        self.import_names = []

    def visit_global(self, node):
        args = "the keyword 'global' is used on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)

    def visit_nonlocal(self, node):
        args = "the keyword 'nonlocal' is used on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)

    def visit_assign(self, node):
        """Allow global constant variables (uppercase), but issue messages for 
        all other globals.
        """
        self._inspect_vars(node)

    def visit_name(self, node):
        """Allow global constant variables (uppercase), but issue messages for 
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
        """Allows constant, global variables (i.e. uppercase), but issue 
        messages for all other global variables.
        """
        if hasattr(node, 'name') and node.name in self.import_names:
            return
        if (isinstance(node.frame(), astroid.scoped_nodes.Module) and not is_in_main(node)):
            node_list = _get_child_disallowed_global_var_nodes(node)
            for node in node_list:
                args = "a global variable '{}' is declared on line {}"\
                    .format(node.name, node.lineno)
                self.add_message('forbidden-global-variables', node=node, args=args)


def _get_child_disallowed_global_var_nodes(node):
    """Return a list of all top-level Name or AssignName nodes for a given 
    global, non-constant variable. 
    """
    node_list = []
    if ((isinstance(node, astroid.AssignName) or (isinstance(node, astroid.Name) and not isinstance(node.parent, astroid.Call))) 
        and not re.match(CONST_NAME_RGX, node.name)):
        return [node]
    for child_node in node.get_children():
        node_list += _get_child_disallowed_global_var_nodes(child_node)
    return node_list


def is_in_main(node):
    if not hasattr(node, 'parent'):
        return False

    parent = node.parent
    try:
        if (isinstance(parent, astroid.node_classes.If) and
              parent.test.left.name == '__name__' and
              parent.test.ops[0][1].value == '__main__'):
            return True
        else:
            return is_in_main(parent)
    except (AttributeError, IndexError) as e:
        return is_in_main(parent)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(GlobalVariablesChecker(linter))
