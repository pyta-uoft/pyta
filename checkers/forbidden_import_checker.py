import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class ForbiddenImportChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'custom'
    msgs = {'E9999':
                ('You may not import any modules - you %s',
                 'forbidden-import',
                 'Used when you use import')}
    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    @check_messages("forbidden-import")
    def visit_import(self, node):
        """visit and Import node"""
        self.add_message('forbidden-import',
                         node=node,
                         args=('imported \033[4;34m%s\033[0m on line %s.' %
                               (', '.join(map(lambda x: x[0], node.names)),
                               node.lineno)))

    @check_messages("forbidden-import")
    def visit_call(self, node):
        if isinstance(node.func, astroid.Name):
            name = node.func.name
            # ignore the name if it's not a builtin (i.e. not defined in the
            # locals nor globals scope)
            if not (name in node.frame() or name in node.root()):
                if name == "__import__":
                    args = "use \033[4;34m__import__\033[0m on line {}".format(node.lineno)
                    # add the message
                    self.add_message('forbidden-import', node=node,
                                     args=args)


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(ForbiddenImportChecker(linter))
