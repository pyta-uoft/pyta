"""checker for use of eval(), compile() or exec().
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers.utils import check_messages
from pylint.checkers import BaseChecker


FORBIDDEN_BUILTIN = ['compile', 'eval', 'exec']


class DynamicExecutionChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'dynamic_execution'
    msgs = {'E9991': ('Used built-in function %s',
                      'dynamic-execution-not-allowed',
                      'Dynamic execution of code is not allowed. You may not use '
                      'built-in functions eval(), compile() or exec().')}

    options = (('functions-not-allowed',
                {'default': FORBIDDEN_BUILTIN,
                 'type': 'csv', 'metavar': '<builtin function names>',
                 'help': 'List of builtins function names that should not be '
                         'used, separated by a comma'}
                ),
               )

    priority = -1


    @check_messages('bad-builtin')
    def visit_call(self, node):
        # Check if the called function is in one of the forbidden buildin functions by using option.
        if isinstance(node.func, astroid.Name) and (node.func.name in self.config.functions_not_allowed):
            args = "{} on line {}".format(node.func.name, node.lineno)
            self.add_message('dynamic-execution-not-allowed', node=node, args=args)


def register(linter):
    """required method to auto register this checker

    :param linter: Main interface object for Pylint plugins
    :type linter: Pylint object
    """
    linter.register_checker(DynamicExecutionChecker(linter))

