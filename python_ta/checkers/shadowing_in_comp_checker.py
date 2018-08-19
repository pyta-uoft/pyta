"""checker for variable shadowing in a comprehension.
"""
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class ShadowingInCompChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'shadowing_in_comp'
    msgs = {'E9988': ("Comprehension loop variable '%s' shadows a variable in an outer scope",
                      'shadowing-in-comp',
                      'Used when there is shadowing inside a comprehension'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages('shadowing-in-comp')
    def visit_comprehension(self, node):
        target = node.target
        if target.name in node.parent.frame().locals:
            args = target.name
            self.add_message('shadowing-in-comp', node=target, args=args)

def register(linter):
    linter.register_checker(ShadowingInCompChecker(linter))
