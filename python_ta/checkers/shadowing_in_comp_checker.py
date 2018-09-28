"""checker for variable shadowing in a comprehension.
"""
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class ShadowingInCompChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'shadowing_inside_comprehension'
    msgs = {'E9988': ("Comprehension variable '%s' shadows a variable in an outer scope",
                      'shadowing-inside-comprehension',
                      'Used when there is shadowing inside a comprehension'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages('shadowing-inside-comprehension')
    def visit_comprehension(self, node: astroid.Comprehension):
        if isinstance(node.target, astroid.Tuple):
            for target in node.target.elts:
                if target.name in node.parent.frame().locals:
                    args = target.name
                    self.add_message('shadowing-inside-comprehension', node=target, args=args)
        else:  # isinstance(node.target, astroid.AssignName)
            if node.target.name in node.parent.frame().locals:
                args = node.target.name
                self.add_message('shadowing-inside-comprehension', node=node.target, args=args)


def register(linter):
    linter.register_checker(ShadowingInCompChecker(linter))
