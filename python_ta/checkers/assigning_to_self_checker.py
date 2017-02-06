"""checker for assigning to self.
"""

import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class AssigningToSelfChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'assigning_to_self'
    msgs = {'E9990': ('Assigning value to self on line %s',
                      'assigning-to-self',
                      'Used when you assign a value to self'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages('assigning-to-self')
    def visit_assign(self, node):
        target = node.targets[0]
        if isinstance(target, astroid.AssignName) and target.name == 'self':
            args = node.lineno
            self.add_message('assigning-to-self', node=node, args=args)


def register(linter):
    linter.register_checker(AssigningToSelfChecker(linter))
