"""checker for variable shadowing in a comprehension.
"""
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class ShadowingInComprehensionChecker(BaseChecker):

    __implements__ = IAstroidChecker

    name = 'shadowing_in_comprehension'
    msgs = {'E9988': ("Comprehension variable '%s' shadows a variable in an outer scope",
                      'shadowing-in-comprehension',
                      'Used when there is shadowing inside a comprehension'),
            }

    # this is important so that your checker is executed before others
    priority = -1

    @check_messages('shadowing-in-comprehension')
    def visit_comprehension(self, node: astroid.Comprehension):
        if isinstance(node.target, astroid.Tuple):
            for target in node.target.elts:
                if target.name in node.parent.frame().locals and target.name != '_':
                    args = target.name
                    self.add_message('shadowing-in-comprehension', node=target, args=args)
        else:  # isinstance(node.target, astroid.AssignName)
            if node.target.name in node.parent.frame().locals and node.target.name != '_':
                args = node.target.name
                self.add_message('shadowing-in-comprehension', node=node.target, args=args)


def register(linter):
    linter.register_checker(ShadowingInComprehensionChecker(linter))
