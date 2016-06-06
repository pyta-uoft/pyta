"""checker for detecting call __import__.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class ImportFunctionChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'forbidden_import_call'
    msgs = {'E9995': ('Call the function __import__ on %s',
                      'func__import__not_allowed',
                      'Used when you  call the function __import__ to import a '
                      'module'),
           }
    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("func__import__not_allowed")
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                if name == "__import__":
                    args = "line {}".format(node.lineno)
                    # add the message
                    self.add_message('func__import__not_allowed', node=node, args=args)

def register(linter):
    linter.register_checker(ImportFunctionChecker(linter))
