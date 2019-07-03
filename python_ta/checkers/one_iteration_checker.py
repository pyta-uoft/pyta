"""checker for a loop that can only ever run for one iteration.
"""
from typing import Union
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages


class OneIterationChecker(BaseChecker):

    __implements__ = IAstroidChecker
    # name is the same as file name but without _checker part
    name = 'one_iteration'
    # use dashes for connecting words in message symbol
    msgs = {'E9996': ('This loop will only ever run for one iteration',
                      'one-iteration',
                      'Reported when the loop body always breaks out of the loop '
                      '(e.g., by returning or using the "break" keyword).'),
           }

    # this is important so that your checker is executed before others
    priority = -1

    # pass in message symbol as a parameter of check_messages
    @check_messages('one-iteration')
    def visit_for(self, node):
        if self._check_one_iteration(node):
            self.add_message('one-iteration', node=node)

    @check_messages('one-iteration')
    def visit_while(self, node):
        if self._check_one_iteration(node):
            self.add_message('one-iteration', node=node)

    def _check_one_iteration(self, node: Union[astroid.For, astroid.While]) -> bool:
        """Return whether the given loop is guaranteed to stop after one iteration."""
        # TODO: Complete this method.
        # print(node.cfg_block)

        return False


def register(linter):
    linter.register_checker(OneIterationChecker(linter))
