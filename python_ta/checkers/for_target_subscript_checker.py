"""Checker for target of for loop in subscript form.
"""
import astroid
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from pylint.interfaces import IAstroidChecker


class ForTargetSubscriptChecker(BaseChecker):
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'for_target_subscript'
    # use dashes for connecting words in message symbol
    msgs = {'E9984': ('For loop variable "%s" should not be a part of a larger object.',
                      'for-target-subscript',
                      'Used when you have a loop variable in a for loop '
                      'that is in subscript form'),
            }
    # this is important so that your checker is executed before others
    priority = -1
    # pass in message symbol as a parameter of check_messages

    @check_messages('for-target-subscript')
    def visit_for(self, node: astroid.For) -> None:
        if isinstance(node.target, astroid.Subscript):
            self.add_message('for-target-subscript',
                             node=node.target, args=node.target.as_string())
        # if there are multiple targets
        elif isinstance(node.target, astroid.Tuple):
            for target in node.target.elts:
                if isinstance(target, astroid.Subscript):
                    self.add_message('for-target-subscript',
                                     node=target, args=target.as_string())


def register(linter):
    linter.register_checker(ForTargetSubscriptChecker(linter))
