"""checker for use of I/O functions.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages

FORBIDDEN_BUILTIN = ['input', 'print', 'open']


class IOFunctionChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'IO_Function'
    msgs = {'E9998': ('Used IO function %s',
                      'IO-function-not-allowed',
                      'Used when you use the IO functions "print", "open" or'
                      '"input". Pylint just try to discourage this usage. '
                      'That doesn\'t mean you can not use it !'),
           }
    options = (('forbidden-io-functions',
                {'default': FORBIDDEN_BUILTIN,
                 'type': 'csv', 'metavar': '<builtin function names>',
                 'help': 'List of builtins function names that should not be '
                         'used, separated by a comma'}
                ),
               ('allowed-io',
                {'default': (),
                 'type': 'csv',
                 'metavar': '<forbidden io>',
                 'help': 'Allowed modules to be imported.'}
                )
               )

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("IO-function-not-allowed")
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                scope = node.scope()
                # TODO: Only FunctionDefs are checked. Include global scope?
                if isinstance(scope, astroid.FunctionDef) and scope.name not in self.config.allowed_io:
                    if name in self.config.forbidden_io_functions:
                        self.add_message('IO-function-not-allowed', node=node,
                                         args=name)


def register(linter):
    linter.register_checker(IOFunctionChecker(linter))
