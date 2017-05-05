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

    def visit_global(self, node):
        args = "you used the keyword 'global' on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)

    def visit_nonlocal(self, node):
        args = "you used the keyword 'nonlocal' on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)

    def visit_assign(self, node):
        """Allow global constant variables (uppercase), but issue messages for 
        all other globals.
        """
        if (isinstance(node.frame(), astroid.scoped_nodes.Module) and not is_in_main(node)):

            node_list = get_disallowed_global_var_nodes(node)
            for node in node_list:
                args = "a global variable '{}' is declared on line {}"\
                    .format(node.name, node.lineno)
                self.add_message('forbidden-global-variables', node=node, args=args)


def get_disallowed_global_var_nodes(node):
    """Return a list of all AssignName nodes for a given global, non-constant 
    variable. 
    """
    node_list = []
    if isinstance(node, astroid.AssignName) and not re.match(CONST_NAME_RGX, node.name):
        return [node]
    for child_node in node.get_children():
        node_list += get_disallowed_global_var_nodes(child_node)
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
