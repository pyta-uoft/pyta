"""checker for global variables

"""
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker

class GlobalVariablesChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'global_variables'
    msgs = {'E9997': ('Used the keyword %s', 'forbidden-global-variables',
                      'Global variables should not be used in CSC108/CSC148')}

    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    def visit_global(self, node):
        args = "'global' on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)

    def visit_nonlocal(self, node):
        args = "'nonlocal' on line {}".format(node.lineno)
        self.add_message('forbidden-global-variables', node=node, args=args)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(GlobalVariablesChecker(linter))
