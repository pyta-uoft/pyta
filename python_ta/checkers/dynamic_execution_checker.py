"""checker for use of I/O functions.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages

FORBIDDEN_BUILTIN = ["compile", "eval", "exec"]


class DynamicExecutionChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'dynamic_execution'
    msgs = {'E9991': ('Dynamic execution is not allowed, you used bad built-in function %s',
                      'dynamic-execution-not-allowed',
                      'Used when you use the dynamic functions "eval", "compile" or'
                      '"exec". '),}

    options = (('forbidden-dynamic-exec',
                {'default': FORBIDDEN_BUILTIN,
                 'type': 'csv', 'metavar': '<builtin function names>',
                 'help': 'List of builtins function names that should not be '
                         'used, separated by a comma'}
                ),
               )

    priority = -1

    @check_messages('dynamic-execution-not-allowed')
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                # if name in FORBIDDEN_BUILTIN:
                if name in self.config.forbidden_dynamic_exec:
                    args = "{} on line {}".format(name, node.lineno)
                    # add the message
                    self.add_message('dynamic-execution-not-allowed', node=node, args=args)


def register(linter):
    """ Required method to auto register this checker.
    @param linter: Main interface object for Pylint plugins
    @rtype linter: Pylint object
    """
    linter.register_checker(DynamicExecutionChecker(linter))
