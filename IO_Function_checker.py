"""checker for use of I/O functions.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class IOFunctionChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'I/O-functions'
    msgs = {'E9998': ('Used I/O function %s',
                      'I/O-function-not-allowed',
                      'Used when you use the I/O functions "print", "open" or'
                      '"input". Pylint just try to discourage this usage. '
                      'That doesn\'t mean you can not use it !'),
           }

    @check_messages("I/O-function-not-allowed")
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                # if name in self.config.io_functions:
                if name == "print" or name == "input" or name == "open":
                    args = "{} on line {}".format(name, node.lineno)
                    # add the message
                    self.add_message('I/O-function-not-allowed', node=node, args=args)


def register(linter):
    """
    Required method to auto register this checker.

    @param linter: Main interface object for Pylint plugins
    @rtype linter: Pylint object
    """
    linter.register_checker(IOFunctionChecker(linter))
