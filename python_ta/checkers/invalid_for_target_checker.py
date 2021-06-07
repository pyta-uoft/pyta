"""Checker for target of for loop in subscript form.
"""
import astroid
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from pylint.interfaces import IAstroidChecker


class InvalidForTargetChecker(BaseChecker):
    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'invalid_for_target'
    # use dashes for connecting words in message symbol
    msgs = {'E9984': ('For loop variable "%s" should not be a part of a larger object.',
                      'invalid-for-target',
                      'Used when you have a loop variable in a for loop '
                      'that is in subscript or object attribute form'),
            }
    # this is important so that your checker is executed before others
    priority = -1
    # pass in message symbol as a parameter of check_messages

    @check_messages('invalid-for-target')
    def visit_for(self, node: astroid.For) -> None:
        if isinstance(node.target, astroid.Subscript):
            self.add_message('invalid-for-target',
                             node=node.target, args=node.target.as_string())
        # if there are multiple targets
        elif isinstance(node.target, astroid.Tuple):
            for target in node.target.elts:
                if isinstance(target, astroid.Subscript):
                    self.add_message('invalid-for-target',
                                     node=target, args=target.as_string())


def register(linter):
    linter.register_checker(InvalidForTargetChecker(linter))
