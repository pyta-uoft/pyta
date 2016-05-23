"""checker for global variables

"""
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
import astroid

class GlobalVariablesChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'global_variables'
    msgs = {'E9997': ('Global variables should not be used in CSC108/CSC148 - %s', 'forbidden-global-variables',
                      '')}

    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    def visit_global(self, node):
        args = "you used the keyword 'global' on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)

    def visit_nonlocal(self, node):
        args = "you used the keyword 'nonlocal' on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)

    def visit_assign(self, node):
        if isinstance(node.frame(), astroid.scoped_nodes.Module):
            # info = str(node.targets[0])
            # x = info.split()
            # print(x)
            args = "you declared global variables on line {}".format(node.lineno)
            self.add_message('forbidden-global-variables', node=node, args=args)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(GlobalVariablesChecker(linter))
