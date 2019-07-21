"""checker for a loop that can only ever run for one iteration.
"""
from typing import Union
import astroid
from pylint.interfaces import IAstroidChecker
from pylint.checkers import BaseChecker
from pylint.checkers.utils import check_messages
from python_ta.cfg.graph import CFGBlock


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
        """Return whether the given loop is guaranteed to stop after one iteration.

        More precisely, Returns False if there exists a direct predecessor
        block `p` to the start of the loop block `s` such that the
        first statement in `p` is a child node of <node> and that there exists a
        path from `s` to `p.

        Note: For `while` loops, 'start of the loop block' refers to the block with
        the test condition (or the first of the blocks that make up test condition).
        For `for` loops, it refers to the block with the assignment target.
        """
        start = node.target if isinstance(node, astroid.For) else node
        preds = start.cfg_block.predecessors

        if preds == []:
            return False

        for pred in preds:
            pred = pred.source
            if node.parent_of(pred.statements[0]) and \
                    self.is_predecessor(pred, start.cfg_block):
                return False
        return True

    def is_predecessor(self, block: CFGBlock, _pred: CFGBlock) -> bool:
        """Returns True if <_pred> is a predecessor of <block>.

        A block <d> is predecessor of block <e> if there exists a path from <d>
        to <e>.

        Preconditions:
            - <_pred> is the start block of the loop.
            - <block>.statements[0] is a child node of the astroid.For/While node.

        Assumption:
            - Since every path from the root to <block> must pass through
        <_pred>, we only need to check one of the paths to see if
        <_pred> is the predecessor of <block>.

        """
        if block is _pred:
            return True
        else:
            for pred in block.predecessors:
                if self.is_predecessor(pred.source, _pred):
                    return True
            return False


def register(linter):
    linter.register_checker(OneIterationChecker(linter))
