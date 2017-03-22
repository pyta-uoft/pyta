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
        if (isinstance(node.frame(), astroid.scoped_nodes.Module) and
                not is_in_main(node)):

            regex = str(node.targets[0])
            s = re.findall('\((.*?)\)', regex)[0]
            a = re.match(CONST_NAME_RGX, s)
            # Raise an error only if it's not a constant
            if a is None:
                args = "you declared the global variable '{}' on line {}".\
                    format(s, node.lineno)
                self.add_message('forbidden-global-variables', node=node,
                                 args=args)


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
