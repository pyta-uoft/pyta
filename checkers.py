from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker


class MyAstroidChecker(BaseChecker):
    __implements__ = IAstroidChecker

    name = 'custom'
    msgs = {'E9999':
                ('You may not import any modules - you imported \033[4;34m%s\033[0m on line %s.',
                 'forbidden-import',
                 # TODO: figure out what this string is for
                 '')}
    options = ()
    # this is important so that your checker is executed before others
    priority = -1

    def visit_import(self, node):
        """visit and Import node"""
        self.add_message('forbidden-import',
                         node=node,
                         args=(', '.join(map(lambda x: x[0], node.names)),
                               node.lineno))


def register(linter):
    """required method to auto register this checker"""
    linter.register_checker(MyAstroidChecker(linter))
