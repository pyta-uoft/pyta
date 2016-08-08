import astroid
import inspect
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from colorama import Fore


class ForbiddenImportChecker(BaseChecker):
    __implements__ = IAstroidChecker

    # \033[4;34m%s\033[0m
    name = 'forbidden import'
    msgs = {'E9999':
                ('You may not import any modules - you imported ' + Fore.BLUE +
                 '%s' + Fore.BLACK + ' on line %s.',
                 'forbidden-import',
                 'Used when you use import')}
    options = (('allowed_import_modules',
                {'default': (),
                 'type': 'csv',
                 'metavar': '<modules>',
                 'help': 'Allowed modules to be imported.'}
                ),)

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("forbidden-import")
    def visit_import(self, node):
        """visit and Import node"""
        temp = [name for name in node.names if name[0] not in self.config.allowed_import_modules]

        if temp != []:
            self.add_message('forbidden-import', node=node, args=(', '.join(map(lambda x: x[0], temp)), node.lineno))

    @check_messages("forbidden-import")
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                if name == "__import__":
                    if node.args[0].value not in self.config.allowed_import_modules:
                        args = (node.args[0].value, node.lineno)
                        # add the message
                        self.add_message('forbidden-import', node=node,
                                         args=args)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(ForbiddenImportChecker(linter))
